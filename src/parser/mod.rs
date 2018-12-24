mod lexer;

use std::fmt;
use std::io;
use self::lexer::Lexer;
use super::*;

pub type Result<T> = ::std::result::Result<T, ParserError>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParserError {
    pub row: usize,
    pub col: usize,
    pub desc: String
}

impl ParserError {
    pub fn new(row: usize, col: usize, desc: String) -> ParserError {
        ParserError { row, col, desc }
    }

    pub fn from_token(t: &TokenInfo, desc: String) -> ParserError {
        ParserError { row: t.row, col: t.col, desc }
    }
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}: {}", self.row, self.col, self.desc)
    }
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
    pub source: String,
    pub row: usize,
    pub col: usize,
    pub token: Token
}

pub struct Parser<I: Iterator<Item = io::Result<u8>>> {
    lexer: Lexer<I>
}

impl<I: Iterator<Item = io::Result<u8>>> Parser<I> {
    pub fn new(source: String, input: I) -> Parser<I> {
        Parser {
            lexer: Lexer::new(source, input, 2)
        }
    }

    pub fn input_mut(&mut self) -> &mut I {
        self.lexer.input_mut()
    }

    pub fn skipline(&mut self) {
        self.lexer.skipline();
    }

    pub fn parse_program(&mut self) -> Result<Program> {
        let mut res = Program::new();
        loop {
            let next = self.parse_process(0)?;
            let t = self.lexer.peek(0)?;
            if let Token::COLONEQ = t.token {
                if let Process::Name(name, args) = Rc::try_unwrap(next).unwrap() {
                    let mut params = Vec::new();
                    for next in args {
                        if let Exp::IdExp(id) = next.as_ref() {
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

    pub fn parse_process(&mut self, prec: i16) -> Result<Rc<Process>> {
        let mut acts = Vec::new();
        loop {
            match (self.lexer.peek(0)?.token, self.lexer.peek(1)?.token) {
                (Token::ID(ref name), _) if name == "i" => {
                    self.lexer.next();
                    let t = self.lexer.peek(0)?;
                    if let Token::DOT = t.token {
                        self.lexer.next();
                    } else {
                        return Err(ParserError::from_token(&t,
                            format!("unexpected {}, expected `.`", t)));
                    }
                    acts.push(Action::Tau);
                },
              | (Token::ID(ref name), _) if name == "e" => {
                    self.lexer.next();
                    let t = self.lexer.peek(0)?;
                    if let Token::DOT = t.token {
                        self.lexer.next();
                    } else {
                        return Err(ParserError::from_token(&t,
                            format!("unexpected {}, expected `.`", t)));
                    }
                    acts.push(Action::Delta);
                },
              | (Token::ID(name), Token::DOT) => {
                    self.lexer.next();
                    self.lexer.next();
                    acts.push(Action::Act(name));
                },
                (Token::ID(name), Token::BANG)
              | (Token::ID(name), Token::QUESTIONMARK)
              | (Token::ID(name), Token::LPAR) => {
                    self.lexer.next();
                    let mut t = self.lexer.peek(0)?;
                    let mut param = None;

                    if let Token::LPAR = t.token {
                        self.lexer.next();
                        param = Some(self.parse_exp(0)?);
                        t = self.lexer.peek(0)?;
                        if let Token::RPAR = t.token {
                            self.lexer.next();
                            t = self.lexer.peek(0)?;
                        } else {
                            return Err(ParserError::from_token(&t,
                                format!("unexpected {}, expected `)`", t)));
                        }
                    }

                    let send = match t.token {
                        Token::BANG => true,
                        Token::QUESTIONMARK => false,
                        _ => {
                            return Err(ParserError::from_token(&t,
                                format!("unexpected {}, expected `!` or `?`", t)));
                        }
                    };

                    self.lexer.next();
                    t = self.lexer.peek(0)?;
                    match (send, t.token) {
                        (false, Token::ID(var)) => {
                            self.lexer.next();
                            t = self.lexer.peek(0)?;
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
                            t = self.lexer.peek(0)?;
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
                ccs! { when (@cond) @p }
            },
            Token::INT(0) => {
                self.lexer.next();
                ccs!{ 0 }
            },
            Token::INT(1) => {
                self.lexer.next();
                ccs!{ 1 }
            },
            Token::ID(id) => {
                self.lexer.next();
                let mut args = Vec::new();

                if let Token::LSQBR = self.lexer.peek(0)?.token {
                    self.lexer.next();
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

                Rc::new(Process::Name(id, args))
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
            res = ccs!{ @act.@res };
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

                    res = Rc::new(Process::Restrict(res, comp, set));
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
                    Token::PLUS => ccs!{ @res + @rhs },
                    Token::PIPE => ccs!{ @res | @rhs },
                    Token::SEMICOLON => ccs!{ @res; @rhs },
                    _ => unreachable!()
                };
            }
        }
    }

    pub fn parse_exp(&mut self, prec: i16) -> Result<Rc<Exp>> {
        let t = self.lexer.peek(0)?;
        let mut res = match t.token {
            Token::PLUS => {
                self.lexer.next();
                ccs_exp!{ +@{self.parse_exp(Token::prec_exp_max())?} }
            },
            Token::MINUS => {
                self.lexer.next();
                ccs_exp!{ -@{self.parse_exp(Token::prec_exp_max())?} }
            },
            Token::BANG => {
                self.lexer.next();
                ccs_exp!{ !@{self.parse_exp(Token::prec_exp_max())?} }
            },
            Token::TRUE => {
                self.lexer.next();
                ccs_exp!{ :true }
            },
            Token::FALSE => {
                self.lexer.next();
                ccs_exp!{ :false }
            },
            Token::INT(num) => {
                self.lexer.next();
                ccs_exp!{ :num }
            },
            Token::STR(s) => {
                self.lexer.next();
                ccs_exp!{ :s }
            },
            Token::ID(id) => {
                self.lexer.next();
                Rc::new(Exp::IdExp(id))
            },
            Token::COLON => {
                self.lexer.next();
                let t = self.lexer.peek(0)?;
                match t.token {
                    Token::INT(num) => {
                        self.lexer.next();
                        ccs_exp!{ :num }
                    },
                    Token::ID(id) => {
                        self.lexer.next();
                        Rc::new(Exp::IdExp(id))
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
                res = match t.token {
                    Token::PLUS => ccs_exp!{ @res + @rhs },
                    Token::MINUS => ccs_exp!{ @res - @rhs },
                    Token::STAR => ccs_exp!{ @res * @rhs },
                    Token::SLASH => ccs_exp!{ @res / @rhs },
                    Token::PERCENT => ccs_exp!{ @res % @rhs },
                    Token::HAT => ccs_exp!{ @res ^ @rhs },
                    Token::LESS => ccs_exp!{ @res < @rhs },
                    Token::LESSEQ => ccs_exp!{ @res <= @rhs },
                    Token::GREATER => ccs_exp!{ @res > @rhs },
                    Token::GREATEREQ => ccs_exp!{ @res >= @rhs },
                    Token::EQEQ => ccs_exp!{ @res == @rhs },
                    Token::BANGEQ => ccs_exp!{ @res != @rhs },
                    Token::ANDAND => ccs_exp!{ @res && @rhs },
                    Token::PIPEPIPE => ccs_exp!{ @res || @rhs },
                    _ => unreachable!()
                };
            }
        }
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
