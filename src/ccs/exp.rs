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
pub enum Exp<ID: Identifier = String> {
    BoolConst(bool),
    IntConst(i64),
    StrConst(String),
    IdExp(ID),
    Unary(UnaryOp, Arc<Exp<ID>>),
    Binary(BinaryOp, Arc<Exp<ID>>, Arc<Exp<ID>>)
}

impl<ID: Identifier> Exp<ID> {
    pub fn eval(&self) -> Result<Value, ID> {
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

    pub fn eval_exp(&self) -> Result<Arc<Exp<ID>>, ID> {
        Ok(match self.eval()? {
            Value::Bool(b) =>
                Arc::new(Exp::BoolConst(b)),
            Value::Int(n) =>
                Arc::new(Exp::IntConst(n)),
            Value::Str(s) =>
                Arc::new(Exp::StrConst(s.clone())),
        })
    }

    pub fn subst<S>(this: &Arc<Exp<ID>>, var: S, val: &Value) -> Arc<Exp<ID>>
        where S: Into<ID>
    {
        let mut subst = HashMap::new();
        subst.insert(var.into(), val);
        Exp::subst_map(this, &subst)
    }

    pub fn subst_map(this: &Arc<Exp<ID>>, subst: &HashMap<ID, &Value>) -> Arc<Exp<ID>> {
        if subst.is_empty() {
            return Arc::clone(this);
        }

        match this.as_ref() {
            Exp::BoolConst(_)
          | Exp::IntConst(_)
          | Exp::StrConst(_) =>
                Arc::clone(this),
            Exp::IdExp(id) =>
                if let Some(val) = subst.get(id) {
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

    pub fn compress(&self, dict: &mut Dict<ID>) -> Arc<Exp<usize>> {
        match self {
            Exp::BoolConst(b) =>
                Arc::new(Exp::BoolConst(*b)),
            Exp::IntConst(n) =>
                Arc::new(Exp::IntConst(*n)),
            Exp::StrConst(s) =>
                Arc::new(Exp::StrConst(s.clone())),
            Exp::IdExp(id) =>
                Arc::new(Exp::IdExp(dict.lookup_insert(id))),
            Exp::Unary(op, exp) =>
                Arc::new(Exp::Unary(*op, exp.compress(dict))),
            Exp::Binary(op, lhs, rhs) =>
                Arc::new(Exp::Binary(*op, lhs.compress(dict), rhs.compress(dict)))
        }
    }

    pub fn uncompress(other: &Exp<usize>, dict: &Dict<ID>) -> Arc<Exp<ID>> {
        match other {
            Exp::BoolConst(b) =>
                Arc::new(Exp::BoolConst(*b)),
            Exp::IntConst(n) =>
                Arc::new(Exp::IntConst(*n)),
            Exp::StrConst(s) =>
                Arc::new(Exp::StrConst(s.clone())),
            Exp::IdExp(id) =>
                Arc::new(Exp::IdExp(dict.index_to_id(*id).clone())),
            Exp::Unary(op, exp) =>
                Arc::new(Exp::Unary(*op, Exp::uncompress(exp, dict))),
            Exp::Binary(op, lhs, rhs) =>
                Arc::new(Exp::Binary(*op, Exp::uncompress(lhs, dict), Exp::uncompress(rhs, dict)))
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

impl<ID> fmt::Display for Exp<ID>
    where ID: Identifier + fmt::Display
{
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

impl<'a, ID> fmt::Display for DisplayCompressed<'a, ID, Exp<usize>>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Exp::BoolConst(b) => write!(f, "{}", b),
            Exp::IntConst(n) => write!(f, "{}", n),
            Exp::StrConst(s) => write!(f, "{:?}", s),
            Exp::IdExp(id) => write!(f, "{}", DisplayCompressed(id, &self.1)),
            Exp::Unary(op, e) => write!(f, "({}{})", op, e),
            Exp::Binary(op, l, r) => write!(f, "({} {} {})", l, op, r)
        }
    }
}

impl<'a, ID> fmt::Display for DisplayCompressed<'a, ID, Arc<Exp<usize>>>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        DisplayCompressed(self.0.as_ref(), self.1).fmt(f)
    }
}
