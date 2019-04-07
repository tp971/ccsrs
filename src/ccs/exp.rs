use super::*;

use std::fmt;
use std::sync::Arc;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Int(i64),
    Str(String)
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum UnaryOp {
    Plus, Minus, Not
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinaryOp {
    Plus, Minus, Star, Slash, Percent, Hat,
    AndAnd, PipePipe,
    EqEq, NEq, LT, LEq, GT, GEq
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Exp {
    BoolConst(bool),
    IntConst(i64),
    StrConst(String),
    IdExp(String),
    Unary(UnaryOp, Arc<Exp>),
    Binary(BinaryOp, Arc<Exp>, Arc<Exp>)
}

impl Exp {
    pub fn eval(&self) -> Result<Value> {
        match self {
            Exp::BoolConst(b) =>
                Ok(Value::Bool(*b)),
            Exp::IntConst(n) =>
                Ok(Value::Int(*n)),
            Exp::StrConst(s) =>
                Ok(Value::Str(s.clone())),
            Exp::IdExp(id) =>
                Err(Error::ExpUnbound(id.clone())),
            Exp::Unary(op, exp) => {
                let val = exp.eval()?;
                match (op, val) {
                    (UnaryOp::Plus, Value::Int(n)) =>
                        Ok(Value::Int(n)),
                    (UnaryOp::Minus, Value::Int(n)) =>
                        Ok(Value::Int(-n)),
                    (UnaryOp::Not, Value::Bool(b)) =>
                        Ok(Value::Bool(!b)),
                    (op, val) =>
                        Err(Error::ExpUnaryError(op.clone(), val))
                }
            }
            Exp::Binary(op, l, r) => {
                let lval = l.eval()?;
                let rval = r.eval()?;
                match (op, lval, rval) {
                    (BinaryOp::Hat, Value::Str(l), Value::Str(r)) =>
                        Ok(Value::Str(l.clone() + &r)),
                    (BinaryOp::Hat, Value::Str(l), Value::Int(r)) =>
                        Ok(Value::Str(format!("{}{}", l, r))),
                    (BinaryOp::Hat, Value::Int(l), Value::Str(r)) =>
                        Ok(Value::Str(format!("{}{}", l, r))),
                    (BinaryOp::Plus, Value::Int(l), Value::Int(r)) =>
                        Ok(Value::Int(l + r)),
                    (BinaryOp::Minus, Value::Int(l), Value::Int(r)) =>
                        Ok(Value::Int(l - r)),
                    (BinaryOp::Star, Value::Int(l), Value::Int(r)) =>
                        Ok(Value::Int(l * r)),
                    (BinaryOp::Slash, Value::Int(l), Value::Int(r)) =>
                        Ok(Value::Int(l / r)),
                    (BinaryOp::Percent, Value::Int(l), Value::Int(r)) =>
                        Ok(Value::Int(l % r)),
                    (BinaryOp::AndAnd, Value::Bool(l), Value::Bool(r)) =>
                        Ok(Value::Bool(l && r)),
                    (BinaryOp::PipePipe, Value::Bool(l), Value::Bool(r)) =>
                        Ok(Value::Bool(l || r)),
                    (BinaryOp::EqEq, Value::Int(l), Value::Int(r)) =>
                        Ok(Value::Bool(l == r)),
                    (BinaryOp::EqEq, Value::Bool(l), Value::Bool(r)) =>
                        Ok(Value::Bool(l == r)),
                    (BinaryOp::NEq, Value::Int(l), Value::Int(r)) =>
                        Ok(Value::Bool(l != r)),
                    (BinaryOp::NEq, Value::Bool(l), Value::Bool(r)) =>
                        Ok(Value::Bool(l != r)),
                    (BinaryOp::LT, Value::Int(l), Value::Int(r)) =>
                        Ok(Value::Bool(l < r)),
                    (BinaryOp::LEq, Value::Int(l), Value::Int(r)) =>
                        Ok(Value::Bool(l <= r)),
                    (BinaryOp::GT, Value::Int(l), Value::Int(r)) =>
                        Ok(Value::Bool(l > r)),
                    (BinaryOp::GEq, Value::Int(l), Value::Int(r)) =>
                        Ok(Value::Bool(l >= r)),
                    (op, lval, rval) =>
                        Err(Error::ExpBinaryError(op.clone(), lval, rval))
                }
            }
        }
    }

    pub fn eval_exp(&self) -> Result<Arc<Exp>> {
        Ok(match self.eval()? {
            Value::Bool(b) =>
                Arc::new(Exp::BoolConst(b)),
            Value::Int(n) =>
                Arc::new(Exp::IntConst(n)),
            Value::Str(s) =>
                Arc::new(Exp::StrConst(s.clone())),
        })
    }

    pub fn subst(this: &Arc<Exp>, var: &str, val: &Value) -> Arc<Exp> {
        let mut subst = HashMap::new();
        subst.insert(var, val);
        Exp::subst_map(this, &subst)
    }

    pub fn subst_map(this: &Arc<Exp>, subst: &HashMap<&str, &Value>) -> Arc<Exp> {
        if subst.is_empty() {
            return Arc::clone(this);
        }

        match this.as_ref() {
            Exp::BoolConst(_)
          | Exp::IntConst(_)
          | Exp::StrConst(_) =>
                Arc::clone(this),
            Exp::IdExp(id) =>
                if let Some(val) = subst.get(&id[..]) {
                    match val {
                        Value::Bool(b) =>
                            Arc::new(Exp::BoolConst(*b)),
                        Value::Int(n) =>
                            Arc::new(Exp::IntConst(*n)),
                        Value::Str(s) =>
                            Arc::new(Exp::StrConst(s.clone()))
                    }
                } else {
                    Arc::clone(this)
                },
            Exp::Unary(op, exp) => {
                let exp2 = Exp::subst_map(exp, subst);
                if Arc::ptr_eq(&exp2, &exp) {
                    Arc::clone(this)
                } else {
                    Arc::new(Exp::Unary(op.clone(), exp2))
                }
            },
            Exp::Binary(op, l, r) => {
                let l2 = Exp::subst_map(l, subst);
                let r2 = Exp::subst_map(r, subst);
                if Arc::ptr_eq(&l2, &l) && Arc::ptr_eq(&r2, &r) {
                    Arc::clone(this)
                } else {
                    Arc::new(Exp::Binary(op.clone(), l2, r2))
                }
            }
        }
    }
}



impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Bool(b) =>
                write!(f, "{}", b),
            Value::Int(n) =>
                write!(f, "{}", n),
            Value::Str(s) =>
                write!(f, "{:?}", s)
        }
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UnaryOp::Plus => write!(f, "+"),
            UnaryOp::Minus => write!(f, "-"),
            UnaryOp::Not => write!(f, "!")
        }
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinaryOp::Plus => write!(f, "+"),
            BinaryOp::Minus => write!(f, "-"),
            BinaryOp::Star => write!(f, "*"),
            BinaryOp::Slash => write!(f, "/"),
            BinaryOp::Percent => write!(f, "%"),
            BinaryOp::Hat => write!(f, "^"),
            BinaryOp::AndAnd => write!(f, "&&"),
            BinaryOp::PipePipe => write!(f, "||"),
            BinaryOp::EqEq => write!(f, "=="),
            BinaryOp::NEq => write!(f, "!="),
            BinaryOp::LT => write!(f, "<"),
            BinaryOp::LEq => write!(f, "<="),
            BinaryOp::GT => write!(f, ">"),
            BinaryOp::GEq => write!(f, ">=")
        }
    }
}

impl fmt::Display for Exp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Exp::BoolConst(b) => write!(f, "{}", b),
            Exp::IntConst(n) => write!(f, "{}", n),
            Exp::StrConst(s) => write!(f, "{:?}", s),
            Exp::IdExp(id) => write!(f, "{}", id),
            Exp::Unary(op, e) => write!(f, "({}{})", op, e),
            Exp::Binary(op, l, r) => write!(f, "({} {} {})", l, op, r)
        }
    }
}
