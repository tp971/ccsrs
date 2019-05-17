mod lexer;
use lexer::Lexer;

use crate::ccs::*;

use std::collections::BTreeSet;
use std::fmt;
use std::io;
use std::sync::Arc;

pub type Result<T> = ::std::result::Result<T, ParserError>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParserError {
    pub loc: Location,
    pub desc: String
}

impl ParserError {
    pub fn new(loc: Location, desc: String) -> ParserError {
        ParserError { loc, desc }
    }

    pub fn from_token(t: &TokenInfo, desc: String) -> ParserError {
        ParserError { loc: t.loc, desc }
    }
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}: {}", self.loc.row, self.loc.col, self.desc)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Location {
    pub row: usize,
    pub col: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token {
    EOF,
    ID(String), INT(i64), STR(String),
    TRUE, FALSE, WHEN,
    LPAR, RPAR, LSQBR, RSQBR, LBRACE, RBRACE,
    DOT, COMMA, COLON, COLONEQ, SEMICOLON, BACKSLASH,
    PLUS, MINUS, STAR, SLASH, PERCENT, HAT,
    BANG, QUESTIONMARK, AND, ANDAND, PIPE, PIPEPIPE,
    LESS, LESSEQ, GREATER, GREATEREQ,
    EQ, EQEQ, BANGEQ,
}

#[derive(Debug, Clone)]
pub struct TokenInfo {
    pub loc: Location,
    pub token: Token
}

impl Location {
    pub fn new(row: usize, col: usize) -> Location {
        Location { row, col }
    }
}

pub struct Parser<I: Iterator<Item = io::Result<u8>>> {
    lexer: Lexer<I>
}

impl<I: Iterator<Item = io::Result<u8>>> Parser<I> {
    pub fn new(input: I) -> Parser<I> {
        Parser {
            lexer: Lexer::new(input, 2)
        }
    }

    pub fn input_mut(&mut self) -> &mut I {
        self.lexer.input_mut()
    }

    pub fn skipline(&mut self) {
        self.lexer.skipline();
    }

    pub fn parse_program(&mut self) -> Result<Program<String>> {
        let mut res = Program::new();
        loop {
            let next = self.parse_process(0)?;
            let t = self.lexer.peek(0)?;
            if let Token::COLONEQ = t.token {
                if let Process::Name(name, args) = next {
                    let mut params = Vec::new();
                    for next in args {
                        if let Exp::IdExp(id) = next {
                            params.push(id.clone());
                        } else {
                            return Err(ParserError::from_token(&t,
                                "unexpected `:=`".to_string()));
                        }
                    }
                    self.lexer.next();
                    res.add_binding(Binding::new(name, params, self.parse_process(0)?));
                } else {
                    return Err(ParserError::from_token(&t,
                        "unexpected `:=`".to_string()));
                }
            } else {
                res.set_process(next);
                break;
            }
        }
        let t = self.lexer.peek(0)?;
        if let Token::EOF = t.token {
            Ok(res)
        } else {
            return Err(ParserError::from_token(&t,
                format!("unexpected {}, expected end of file", t)));
        }
    }

    pub fn parse_process(&mut self, prec: i16) -> Result<Process<String>> {
        let mut acts = Vec::new();
        loop {
            let t_name = self.lexer.peek(0)?;
            match (t_name.token, self.lexer.peek(1)?.token) {
                (Token::ID(name), Token::DOT) => {
                    self.lexer.next();
                    self.lexer.next();
                    if name == "i" {
                        acts.push(Action::Tau);
                    } else if name == "e" {
                        acts.push(Action::Delta);
                    } else {
                        acts.push(Action::Act(name));
                    }
                },
                (Token::ID(name), t2 @ Token::BANG)
              | (Token::ID(name), t2 @ Token::QUESTIONMARK)
              | (Token::ID(name), t2 @ Token::LPAR) => {
                    self.lexer.next();

                    let param = if let Token::LPAR = t2 {
                        Some(self.parse_exp(0)?)
                    } else {
                        None
                    };

                    let t = self.lexer.peek(0)?;
                    let send = match t.token {
                        Token::BANG => true,
                        Token::QUESTIONMARK => false,
                        _ => {
                            return Err(ParserError::from_token(&t,
                                format!("unexpected {}, expected `!` or `?`", t)));
                        }
                    };

                    self.lexer.next();
                    match (send, self.lexer.peek(0)?.token) {
                        (false, Token::ID(var)) => {
                            self.lexer.next();
                            let t = self.lexer.peek(0)?;
                            if let Token::DOT = t.token {
                                self.lexer.next();
                                acts.push(Action::RecvInto(name, param, var));
                            } else {
                                return Err(ParserError::from_token(&t,
                                    format!("unexpected {}, expected `.`", t)));
                            }
                        }
                        (_, Token::DOT) => {
                            self.lexer.next();
                            if send {
                                acts.push(Action::Snd(name, param, None));
                            } else {
                                acts.push(Action::Recv(name, param, None));
                            }
                        },
                        (_, _) => {
                            let exp = self.parse_exp(0)?;
                            let t = self.lexer.peek(0)?;
                            if let Token::DOT = t.token {
                                self.lexer.next();
                                if send {
                                    acts.push(Action::Snd(name, param, Some(exp)));
                                } else {
                                    acts.push(Action::Recv(name, param, Some(exp)));
                                }
                            } else {
                                return Err(ParserError::from_token(&t,
                                    format!("unexpected {}, expected `.`", t)));
                            }
                        }
                    }
                },
                _ => {
                    break;
                }
            }
        }

        let t = self.lexer.peek(0)?;
        let mut res = match t.token {
            Token::WHEN => {
                self.lexer.next();
                let cond = self.parse_exp(0)?;
                let p = self.parse_process(Token::prec_proc_max())?;
                Process::When(cond, Arc::new(p))
            },
            Token::INT(0) => {
                self.lexer.next();
                Process::Null
            },
            Token::INT(1) => {
                self.lexer.next();
                Process::Term
            },
            Token::ID(id) => {
                self.lexer.next();
                let mut args = Vec::new();

                if let Token::LSQBR = self.lexer.peek(0)?.token {
                    self.lexer.next();
                    if let Token::RSQBR = self.lexer.peek(0)?.token {
                        self.lexer.next();
                    } else {
                        loop {
                            args.push(self.parse_exp(0)?);
                            let t = self.lexer.peek(0)?;
                            match t.token {
                                Token::COMMA => {
                                    self.lexer.next();
                                },
                                Token::RSQBR => {
                                    self.lexer.next();
                                    break;
                                },
                                _ =>
                                    return Err(ParserError::from_token(&t,
                                        format!("unexpected {}, expected `,` or `]`", t)))
                            }
                        }
                    }
                }

                Process::Name(id, args)
            },
            Token::LPAR => {
                self.lexer.next();
                let res = self.parse_process(0)?;
                let t = self.lexer.peek(0)?;
                if let Token::RPAR = t.token {
                    self.lexer.next();
                    res
                } else {
                    return Err(ParserError::from_token(&t,
                        format!("unexpected {}, expected `)`", t)))
                }
            },
            _ =>
                return Err(ParserError::from_token(&t,
                    format!("unexpected {}, expected `0`, `1` or identifier", t)))
        };

        while let Some(act) = acts.pop() {
            res = Process::Prefix(act, Arc::new(res));
        }

        let mut t = self.lexer.peek(0)?;
        loop {
            match t.token {
                Token::SLASH | Token::BACKSLASH => {
                    self.lexer.next();
                    t = self.lexer.peek(0)?;
                    if let Token::LBRACE = t.token {
                        self.lexer.next();
                        t = self.lexer.peek(0)?;
                    } else {
                        return Err(ParserError::from_token(&t,
                            format!("unexpected {}, expected `{{`", t)))
                    }

                    let mut comp = false;
                    let mut set = BTreeSet::new();
                    loop {
                        match t.token {
                            Token::RBRACE if !comp && set.is_empty() => {
                                self.lexer.next();
                                break;
                            }
                            Token::STAR if !comp && set.is_empty() => {
                                self.lexer.next();
                                t = self.lexer.peek(0)?;
                                comp = true;
                                match t.token {
                                    Token::RBRACE => {
                                        self.lexer.next();
                                        t = self.lexer.peek(0)?;
                                        break;
                                    },
                                    Token::COMMA => {
                                        self.lexer.next();
                                        t = self.lexer.peek(0)?;
                                    },
                                    _ =>
                                        return Err(ParserError::from_token(&t,
                                            format!("unexpected {}, expected `,` or `}}`", t)))
                                }
                            },
                            Token::ID(id) => {
                                self.lexer.next();
                                t = self.lexer.peek(0)?;
                                set.insert(id);
                                match t.token {
                                    Token::RBRACE => {
                                        self.lexer.next();
                                        t = self.lexer.peek(0)?;
                                        break;
                                    },
                                    Token::COMMA => {
                                        self.lexer.next();
                                        t = self.lexer.peek(0)?;
                                    },
                                    _ =>
                                        return Err(ParserError::from_token(&t,
                                            format!("unexpected {}, expected `,` or `}}`", t)))
                                }
                            },
                            _ =>
                                return Err(ParserError::from_token(&t,
                                    format!("unexpected {}, expected identifier", t)))
                        }
                    }

                    res = Process::Restrict(Arc::new(res), comp, set);
                },
                _ => break
            }
        }

        loop {
            t = self.lexer.peek(0)?;
            let (lprec, rprec) = t.token.prec_proc();
            if lprec < prec {
                return Ok(res);
            } else {
                self.lexer.next();
                let rhs = self.parse_process(rprec)?;
                res = match t.token {
                    Token::PLUS => Process::Choice(Arc::new(res), Arc::new(rhs)),
                    Token::PIPE => Process::Parallel(Arc::new(res), Arc::new(rhs)),
                    Token::SEMICOLON => Process::Sequential(Arc::new(res), Arc::new(rhs)),
                    _ => unreachable!()
                };
            }
        }
    }

    pub fn parse_exp(&mut self, prec: i16) -> Result<Exp<String>> {
        let t = self.lexer.peek(0)?;
        let mut res = match t.token {
            Token::PLUS => {
                self.lexer.next();
                Exp::Unary(UnaryOp::Plus, Arc::new(
                    self.parse_exp(Token::prec_exp_max())?
                ))
            },
            Token::MINUS => {
                self.lexer.next();
                Exp::Unary(UnaryOp::Minus, Arc::new(
                    self.parse_exp(Token::prec_exp_max())?
                ))
            },
            Token::BANG => {
                self.lexer.next();
                Exp::Unary(UnaryOp::Not, Arc::new(
                    self.parse_exp(Token::prec_exp_max())?
                ))
            },
            Token::TRUE => {
                self.lexer.next();
                Exp::from(true)
            },
            Token::FALSE => {
                self.lexer.next();
                Exp::from(false)
            },
            Token::INT(num) => {
                self.lexer.next();
                Exp::from(num)
            },
            Token::STR(s) => {
                self.lexer.next();
                Exp::from(s)
            },
            Token::ID(id) => {
                self.lexer.next();
                Exp::IdExp(id)
            },
            Token::COLON => {
                self.lexer.next();
                let t = self.lexer.peek(0)?;
                match t.token {
                    Token::INT(num) => {
                        self.lexer.next();
                        Exp::from(num)
                    },
                    Token::ID(id) => {
                        self.lexer.next();
                        Exp::IdExp(id)
                    },
                    _ =>
                        return Err(ParserError::from_token(&t,
                            format!("unexpected {}, expected constant or identifier", t)))
                }
            }
            Token::LPAR => {
                self.lexer.next();
                let res = self.parse_exp(0)?;
                let t = self.lexer.peek(0)?;
                if let Token::RPAR = t.token {
                    self.lexer.next();
                    res
                } else {
                    return Err(ParserError::from_token(&t,
                        format!("unexpected {}, expected `)`", t)))
                }
            },
            _ =>
                return Err(ParserError::from_token(&t,
                    format!("unexpected {}, expected constant, identifier or `(`", t)))
        };

        loop {
            let t = self.lexer.peek(0)?;
            let (lprec, rprec) = t.token.prec_exp();
            if lprec < prec {
                return Ok(res);
            } else {
                self.lexer.next();
                let rhs = self.parse_exp(rprec)?;
                let op = match t.token {
                    Token::PLUS => BinaryOp::Plus,
                    Token::MINUS => BinaryOp::Minus,
                    Token::STAR => BinaryOp::Star,
                    Token::SLASH => BinaryOp::Slash,
                    Token::PERCENT => BinaryOp::Percent,
                    Token::HAT => BinaryOp::Hat,
                    Token::LESS => BinaryOp::LT,
                    Token::LESSEQ => BinaryOp::LEq,
                    Token::GREATER => BinaryOp::GT,
                    Token::GREATEREQ => BinaryOp::GEq,
                    Token::EQEQ => BinaryOp::EqEq,
                    Token::BANGEQ => BinaryOp::NEq,
                    Token::ANDAND => BinaryOp::AndAnd,
                    Token::PIPEPIPE => BinaryOp::PipePipe,
                    _ => unreachable!()
                };
                res = Exp::Binary(op, Arc::new(res), Arc::new(rhs));
            }
        }
    }
}

impl Token {
    pub fn prec_proc(&self) -> (i16, i16) {
        match self {
            Token::SEMICOLON => (0, 1),
            Token::PIPE => (2, 3),
            Token::PLUS => (4, 5),
            _ => (-1, -1)
        }
    }

    pub fn prec_proc_max() -> i16 {
        6
    }

    pub fn prec_exp(&self) -> (i16, i16) {
        match self {
            Token::PIPEPIPE =>
                (0, 1),
            Token::ANDAND =>
                (2, 3),
            Token::EQEQ | Token::BANGEQ =>
                (4, 5),
            Token::LESS | Token::LESSEQ | Token::GREATER | Token::GREATEREQ =>
                (6, 7),
            Token::HAT =>
                (8, 9),
            Token::PLUS | Token::MINUS =>
                (10, 11),
            Token::STAR | Token::SLASH | Token::PERCENT =>
                (12, 13),
            _ =>
                (-1, -1)
        }
    }

    pub fn prec_exp_max() -> i16 {
        12
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::EOF => write!(f, "end of file"),
            Token::ID(id) => write!(f, "{}", id),
            Token::INT(num) => write!(f, "{}", num),
            Token::STR(s) => write!(f, "{:?}", s),
            Token::TRUE => write!(f, "true"),
            Token::FALSE => write!(f, "false"),
            Token::WHEN => write!(f, "when"),
            Token::LPAR => write!(f, "("),
            Token::RPAR => write!(f, ")"),
            Token::LSQBR => write!(f, "["),
            Token::RSQBR => write!(f, "]"),
            Token::LBRACE => write!(f, "{{"),
            Token::RBRACE => write!(f, "}}"),
            Token::DOT => write!(f, "."),
            Token::COMMA => write!(f, ","),
            Token::COLON => write!(f, ":"),
            Token::COLONEQ => write!(f, ":="),
            Token::SEMICOLON => write!(f, ";"),
            Token::BACKSLASH => write!(f, "\\"),
            Token::PLUS => write!(f, "+"),
            Token::MINUS => write!(f, "-"),
            Token::STAR => write!(f, "*"),
            Token::SLASH => write!(f, "/"),
            Token::PERCENT => write!(f, "%"),
            Token::HAT => write!(f, "^"),
            Token::BANG => write!(f, "!"),
            Token::QUESTIONMARK => write!(f, "?"),
            Token::AND => write!(f, "&"),
            Token::ANDAND => write!(f, "&&"),
            Token::PIPE => write!(f, "|"),
            Token::PIPEPIPE => write!(f, "||"),
            Token::LESS => write!(f, "<"),
            Token::LESSEQ => write!(f, "<="),
            Token::GREATER => write!(f, ">"),
            Token::GREATEREQ => write!(f, ">="),
            Token::EQ => write!(f, "="),
            Token::EQEQ => write!(f, "=="),
            Token::BANGEQ => write!(f, "!="),
        }
    }
}

impl fmt::Display for TokenInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.token {
            Token::EOF => 
                write!(f, "end of file"),
            Token::ID(id) => 
                write!(f, "identifier `{}`", id),
            _ =>
                write!(f, "`{}`", self.token)
        }
    }
}
