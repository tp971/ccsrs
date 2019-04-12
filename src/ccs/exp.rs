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
            Exp::Unary(op, exp) =>
                Exp::eval_unary(*op, exp.eval()?),
            Exp::Binary(op, l, r) =>
                Exp::eval_binary(*op, l.eval()?, r.eval()?)
        }
    }

    pub fn _fold_min(&self) -> Option<Value> {
        match self {
            Exp::BoolConst(b) =>
                Some(Value::Bool(*b)),
            Exp::IntConst(n) =>
                Some(Value::Int(*n)),
            Exp::StrConst(s) =>
                Some(Value::Str(s.clone())),
            Exp::IdExp(_) =>
                None,
            Exp::Unary(op, exp) =>
                match exp._fold_min_inner() {
                    Some(val) =>
                        Exp::<ID>::eval_unary(*op, val).ok(),
                    None =>
                        None
                },
            Exp::Binary(op, l, r) =>
                match (l._fold_min_inner(), r._fold_min_inner()) {
                    (Some(lval), Some(rval)) =>
                        Exp::<ID>::eval_binary(*op, lval, rval).ok(),
                    _ =>
                        None
                }
        }
    }

    pub fn _fold_min_inner(&self) -> Option<Value> {
        match self {
            Exp::BoolConst(b) =>
                Some(Value::Bool(*b)),
            Exp::IntConst(n) =>
                Some(Value::Int(*n)),
            Exp::StrConst(s) =>
                Some(Value::Str(s.clone())),
            _ =>
                None
        }
    }

    pub fn eval_unary(op: UnaryOp, val: Value) -> Result<Value, ID> {
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

    pub fn eval_binary(op: BinaryOp, lval: Value, rval: Value) -> Result<Value, ID> {
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

    pub fn subst<S>(&self, var: S, val: &Value, fold: &FoldOptions) -> Exp<ID>
        where S: Into<ID>
    {
        let mut subst = HashMap::new();
        subst.insert(var.into(), val);
        self.subst_map_opt(&subst, fold).unwrap_or_else(|| self.clone())
    }

    pub fn subst_map(&self, subst: &HashMap<ID, &Value>, fold: &FoldOptions) -> Exp<ID> {
        self.subst_map_opt(subst, fold).unwrap_or_else(|| self.clone())
    }

    pub fn subst_opt<S>(&self, var: S, val: &Value, fold: &FoldOptions) -> Option<Exp<ID>>
        where S: Into<ID>
    {
        let mut subst = HashMap::new();
        subst.insert(var.into(), val);
        self.subst_map_opt(&subst, fold)
    }

    pub fn subst_map_opt(&self, subst: &HashMap<ID, &Value>, fold: &FoldOptions) -> Option<Exp<ID>> {
        if subst.is_empty() {
            return None;
        }

        match self {
            Exp::BoolConst(_)
          | Exp::IntConst(_)
          | Exp::StrConst(_) =>
                None,
            Exp::IdExp(id) =>
                if let Some(val) = subst.get(id) {
                    match val {
                        Value::Bool(b) =>
                            Some(Exp::BoolConst(*b)),
                        Value::Int(n) =>
                            Some(Exp::IntConst(*n)),
                        Value::Str(s) =>
                            Some(Exp::StrConst(s.clone()))
                    }
                } else {
                    None
                },
            Exp::Unary(op, exp) => {
                match exp.subst_map_opt(subst, fold) {
                    None =>
                        None,
                    Some(exp2) => {
                        let res = Exp::Unary(op.clone(), Arc::new(exp2));
                        if fold.fold_exp {
                            if let Some(val) = res._fold_min() {
                                return Some(val.into());
                            }
                        }
                        Some(res)
                    }
                }
            },
            Exp::Binary(op, l, r) => {
                match (l.subst_map_opt(subst, fold), r.subst_map_opt(subst, fold)) {
                    (None, None) =>
                        None,
                    (l2, r2) => {
                        let l2 = l2.map_or_else(|| Arc::clone(l), |l2| Arc::new(l2));
                        let r2 = r2.map_or_else(|| Arc::clone(r), |r2| Arc::new(r2));
                        let res = Exp::Binary(op.clone(), l2, r2);
                        if fold.fold_exp {
                            if let Some(val) = res._fold_min() {
                                return Some(val.into());
                            }
                        }
                        Some(res)
                    }
                }
            }
        }
    }

    pub fn compress(&self, dict: &mut Dict<ID>) -> Exp<usize> {
        match self {
            Exp::BoolConst(b) =>
                Exp::BoolConst(*b),
            Exp::IntConst(n) =>
                Exp::IntConst(*n),
            Exp::StrConst(s) =>
                Exp::StrConst(s.clone()),
            Exp::IdExp(id) =>
                Exp::IdExp(dict.lookup_insert(id)),
            Exp::Unary(op, exp) =>
                Exp::Unary(*op, Arc::new(exp.compress(dict))),
            Exp::Binary(op, lhs, rhs) =>
                Exp::Binary(*op, Arc::new(lhs.compress(dict)), Arc::new(rhs.compress(dict)))
        }
    }

    pub fn uncompress(other: &Exp<usize>, dict: &Dict<ID>) -> Exp<ID> {
        match other {
            Exp::BoolConst(b) =>
                Exp::BoolConst(*b),
            Exp::IntConst(n) =>
                Exp::IntConst(*n),
            Exp::StrConst(s) =>
                Exp::StrConst(s.clone()),
            Exp::IdExp(id) =>
                Exp::IdExp(dict.index_to_id(*id).clone()),
            Exp::Unary(op, exp) =>
                Exp::Unary(*op, Arc::new(Exp::uncompress(exp, dict))),
            Exp::Binary(op, lhs, rhs) =>
                Exp::Binary(*op, Arc::new(Exp::uncompress(lhs, dict)), Arc::new(Exp::uncompress(rhs, dict)))
        }
    }
}

impl<ID: Identifier> From<Value> for Exp<ID> {
    fn from(val: Value) -> Exp<ID> {
        match val {
            Value::Bool(b) =>
                Exp::BoolConst(b),
            Value::Int(n) =>
                Exp::IntConst(n),
            Value::Str(s) =>
                Exp::StrConst(s)
        }
    }
}

impl<ID: Identifier> From<&Value> for Exp<ID> {
    fn from(val: &Value) -> Exp<ID> {
        match val {
            Value::Bool(b) =>
                Exp::BoolConst(*b),
            Value::Int(n) =>
                Exp::IntConst(*n),
            Value::Str(s) =>
                Exp::StrConst(s.clone()),
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
            Exp::IdExp(id) => write!(f, "{}", DisplayCompressed(id, self.1)),
            Exp::Unary(op, e) => write!(f, "({}{})", op, DisplayCompressed(e.as_ref(), self.1)),
            Exp::Binary(op, l, r) => write!(f, "({} {} {})", DisplayCompressed(l.as_ref(), self.1), op, DisplayCompressed(r.as_ref(), self.1))
        }
    }
}
