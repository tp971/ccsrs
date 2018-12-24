//#![feature(trace_macros)]
//trace_macros!(true);

pub mod boxed;
pub mod parser;

#[macro_use]
pub mod macros;

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

type Result<T> = std::result::Result<T, Error>;

pub enum Error {
    ExpUnbound(String),
    ExpUnaryError(UnaryOp, Value),
    ExpBinaryError(BinaryOp, Value, Value),
    ExpProcessArgs(String, Vec<String>, Vec<Value>),
    Unbound(String),
    Unguarded(String),
    UnrestrictedInput(String),
    WhenError(Value)
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum UnaryOp {
    Plus, Minus, Not
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum BinaryOp {
    Plus, Minus, Star, Slash, Percent, Hat,
    AndAnd, PipePipe,
    EqEq, NEq, LT, LEq, GT, GEq
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Exp {
    BoolConst(bool),
    IntConst(i64),
    StrConst(String),
    IdExp(String),
    Unary(UnaryOp, Rc<Exp>),
    Binary(BinaryOp, Rc<Exp>, Rc<Exp>)
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Action {
    Tau,
    Delta,
    Act(String),
    Snd(String, Option<Rc<Exp>>, Option<Rc<Exp>>),
    Recv(String, Option<Rc<Exp>>, Option<Rc<Exp>>),
    RecvInto(String, Option<Rc<Exp>>, String)
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Process {
    Null,
    Term,
    Name(String, Vec<Rc<Exp>>),
    Prefix(Action, Rc<Process>),
    Choice(Rc<Process>, Rc<Process>),
    Parallel(Rc<Process>, Rc<Process>),
    Sequential(Rc<Process>, Rc<Process>),
    Restrict(Rc<Process>, bool, BTreeSet<String>), //process, complement, restriction set
    When(Rc<Exp>, Rc<Process>)
}

#[derive(Clone, Debug)]
pub struct Binding {
    pub(crate) name: String,
    pub(crate) args: Vec<String>,
    pub(crate) process: Rc<Process>
}

#[derive(Clone, Debug, Default)]
pub struct Program {
    pub(crate) bindings: HashMap<String, Binding>,
    pub(crate) process: Option<Rc<Process>>
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Transition {
    pub act: Action,
    pub to: Rc<Process>
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Int(i64),
    Str(String)
}

pub enum Side {
    Left, Right
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

    pub fn eval_exp(&self) -> Result<Rc<Exp>> {
        Ok(match self.eval()? {
            Value::Bool(b) =>
                Rc::new(Exp::BoolConst(b)),
            Value::Int(n) =>
                Rc::new(Exp::IntConst(n)),
            Value::Str(s) =>
                Rc::new(Exp::StrConst(s.clone())),
        })
    }

    pub fn subst(this: &Rc<Exp>, var: &str, val: &Value) -> Rc<Exp> {
        match this.as_ref() {
            Exp::BoolConst(_)
          | Exp::IntConst(_)
          | Exp::StrConst(_) =>
                Rc::clone(this),
            Exp::IdExp(id) =>
                if id == var {
                    match val {
                        Value::Bool(b) =>
                            Rc::new(Exp::BoolConst(*b)),
                        Value::Int(n) =>
                            Rc::new(Exp::IntConst(*n)),
                        Value::Str(s) =>
                            Rc::new(Exp::StrConst(s.clone()))
                    }
                } else {
                    Rc::clone(this)
                },
            Exp::Unary(op, exp) => {
                let exp2 = Exp::subst(exp, var, val);
                if Rc::ptr_eq(&exp2, &exp) {
                    Rc::clone(this)
                } else {
                    Rc::new(Exp::Unary(op.clone(), exp2))
                }
            },
            Exp::Binary(op, l, r) => {
                let l2 = Exp::subst(l, var, val);
                let r2 = Exp::subst(r, var, val);
                if Rc::ptr_eq(&l2, &l) && Rc::ptr_eq(&r2, &r) {
                    Rc::clone(this)
                } else {
                    Rc::new(Exp::Binary(op.clone(), l2, r2))
                }
            }
        }
    }
}

impl Action {
    pub fn sync(&self, other: &Action) -> Result<Option<Option<(Side, String, Value)>>> {
        //eprintln!("TRY SYNC: {} ||| {}", self, other);
        match (self, other) {
            (Action::Snd(name1, param1, exp1), Action::Recv(name2, param2, exp2))
          | (Action::Recv(name2, param2, exp2), Action::Snd(name1, param1, exp1)) => {
                if name1 != name2 {
                    return Ok(None);
                }
                match (param1, param2) {
                    (Some(param1), Some(param2)) => {
                        if param1.eval()? != param2.eval()? {
                            return Ok(None);
                        }
                    },
                    (None, None) => {},
                    _ => { return Ok(None); }
                }
                match (exp1, exp2) {
                    (Some(exp1), Some(exp2)) => {
                        if exp1.eval()? != exp2.eval()? {
                            return Ok(None);
                        }
                    },
                    (None, None) => {},
                    _ => { return Ok(None); }
                }
                Ok(Some(None))
            }

            (Action::Snd(name1, param1, Some(exp)), Action::RecvInto(name2, param2, var))
          | (Action::RecvInto(name2, param2, var), Action::Snd(name1, param1, Some(exp))) => {
                if name1 != name2 {
                    return Ok(None);
                }
                match (param1, param2) {
                    (Some(param1), Some(param2)) => {
                        if param1.eval()? != param2.eval()? {
                            return Ok(None);
                        }
                    },
                    (None, None) => {},
                    _ => { return Ok(None); }
                }
                if let Action::RecvInto(_, _, _) = self {
                    Ok(Some(Some((Side::Left, var.clone(), exp.eval()?))))
                } else {
                    Ok(Some(Some((Side::Right, var.clone(), exp.eval()?))))
                }
            },

            _ =>
                Ok(None)
        }
    }

    pub fn observe(&self) -> Option<&str> {
        match self {
            Action::Act(name) | Action::Snd(name, _, _) | Action::Recv(name, _, _) | Action::RecvInto(name, _, _) =>
                Some(name),
            _ =>
                None
        }
    }

    pub fn subst(&self, var: &str, val: &Value) -> Action {
        match self {
            Action::Tau
          | Action::Delta
          | Action::Act(_)
          | Action::Snd(_, None, None)
          | Action::Recv(_, None, None)
          | Action::RecvInto(_, None, _) =>
                self.clone(),

            Action::Snd(name, None, Some(exp)) =>
                Action::Snd(name.clone(), None, Some(Exp::subst(exp, var, val))),
            Action::Snd(name, Some(param), None) =>
                Action::Snd(name.clone(), Some(Exp::subst(param, var, val)), None),
            Action::Snd(name, Some(param), Some(exp)) =>
                Action::Snd(name.clone(), Some(Exp::subst(param, var, val)), Some(Exp::subst(exp, var, val))),

            Action::Recv(name, None, Some(exp)) =>
                Action::Recv(name.clone(), None, Some(Exp::subst(exp, var, val))),
            Action::Recv(name, Some(param), None) =>
                Action::Recv(name.clone(), Some(Exp::subst(param, var, val)), None),
            Action::Recv(name, Some(param), Some(exp)) =>
                Action::Recv(name.clone(), Some(Exp::subst(param, var, val)), Some(Exp::subst(exp, var, val))),

            Action::RecvInto(name, Some(param), var2) =>
                Action::RecvInto(name.clone(), Some(Exp::subst(param, var, val)), var2.clone()),
        }
    }

    pub fn eval(&self) -> Result<Action> {
        match self {
            Action::Tau
          | Action::Delta
          | Action::Act(_)
          | Action::Snd(_, None, None)
          | Action::Recv(_, None, None)
          | Action::RecvInto(_, None, _) =>
                Ok(self.clone()),

            Action::Snd(name, None, Some(exp)) =>
                Ok(Action::Snd(name.clone(), None, Some(exp.eval_exp()?))),
            Action::Snd(name, Some(param), None) =>
                Ok(Action::Snd(name.clone(), Some(param.eval_exp()?), None)),
            Action::Snd(name, Some(param), Some(exp)) =>
                Ok(Action::Snd(name.clone(), Some(param.eval_exp()?), Some(exp.eval_exp()?))),

            Action::Recv(name, None, Some(exp)) =>
                Ok(Action::Recv(name.clone(), None, Some(exp.eval_exp()?))),
            Action::Recv(name, Some(param), None) =>
                Ok(Action::Recv(name.clone(), Some(param.eval_exp()?), None)),
            Action::Recv(name, Some(param), Some(exp)) =>
                Ok(Action::Recv(name.clone(), Some(param.eval_exp()?), Some(exp.eval_exp()?))),

            Action::RecvInto(name, Some(param), var) =>
                Ok(Action::RecvInto(name.clone(), Some(param.eval_exp()?), var.clone()))
        }
    }
}

impl Transition {
    pub fn new(act: Action, to: Rc<Process>) -> Transition {
        Transition { act, to }
    }
}

impl Process {
    pub fn get_transitions(&self, program: &Program) -> Result<HashSet<Transition>> {
        let mut res = HashSet::new();
        let trans = self._get_transitions(program, HashSet::new())?;
        for next in trans.into_iter() {
            if let Action::RecvInto(name, _, _) = &next.act {
                return Err(Error::UnrestrictedInput(name.clone()));
            }
            res.insert(next);
        }
        Ok(res)
    }

    fn _get_transitions(&self, program: &Program, mut seen: HashSet<String>) -> Result<Vec<Transition>> {
        match self {
            Process::Null => {
                Ok(Vec::new())
            },
            Process::Term => {
                let mut set = Vec::new();
                set.push(Transition::new(
                    ccs_act!{ e }, ccs!{ 0 }));
                Ok(set)
            },
            Process::Name(name, args) => {
                if seen.contains(name) {
                    return Err(Error::Unguarded(name.clone()));
                }
                match program.binding(name) {
                    Some(bind) => {
                        seen.insert(name.clone());
                        let mut values = Vec::new();
                        for next in args {
                            values.push(next.eval()?);
                        }
                        Ok(bind.instantiate(&values)?._get_transitions(program, seen)?)
                    },
                    None =>
                        Err(Error::Unbound(name.clone()))
                }
            },
            Process::Prefix(act, p) => {
                let mut set = Vec::new();
                set.push(Transition::new(
                    act.eval()?, Rc::clone(p)
                ));
                Ok(set)
            },
            Process::Choice(l, r) => {
                let mut set = Vec::new();
                for next in l._get_transitions(program, seen.clone())? {
                    set.push(Transition::new(
                        next.act, next.to
                    ));
                }
                for next in r._get_transitions(program, seen)? {
                    set.push(Transition::new(
                        next.act, next.to
                    ));
                }
                Ok(set)
            },
            Process::Parallel(l, r) => {
                let mut set = Vec::new();
                let trans_l = l._get_transitions(program, seen.clone())?;
                let trans_r = r._get_transitions(program, seen)?;
                for l in trans_l.iter() {
                    for r in trans_r.iter() {
                        match l.act.sync(&r.act)? {
                            None => {},
                            Some(None) => {
                                //println!("SYNC: {} ||| {}", l.act, r.act);
                                set.push(Transition::new(
                                    ccs_act!{ i }, ccs!{ @{Rc::clone(&l.to)} | @{Rc::clone(&r.to)} }
                                ));
                            },
                            Some(Some((Side::Left, var, val))) => {
                                //println!("SYNC: {} ||| {}", l.act, r.act);
                                set.push(Transition::new(
                                    ccs_act!{ i }, ccs!{ @{Process::subst(&l.to, &var, &val)} | @{Rc::clone(&r.to)} }
                                ));
                            },
                            Some(Some((Side::Right, var, val))) => {
                                //println!("SYNC: {} ||| {}", l.act, r.act);
                                set.push(Transition::new(
                                    ccs_act!{ i }, ccs!{ @{Rc::clone(&l.to)} | @{Process::subst(&r.to, &var, &val)} }
                                ));
                            }
                        }

                        if let (Action::Delta, Action::Delta) = (&l.act, &r.act) {
                            set.push(Transition::new(
                                ccs_act!{ e }, ccs!{ @{Rc::clone(&l.to)} | @{Rc::clone(&r.to)} }
                            ));
                        }
                    }
                }
                for next in trans_l {
                    if let Action::Delta = &next.act {
                        continue;
                    }
                    set.push(Transition::new(
                        next.act, ccs!{ @{next.to} | @{Rc::clone(r)} }
                    ));
                }
                for next in trans_r {
                    if let Action::Delta = &next.act {
                        continue;
                    }
                    set.push(Transition::new(
                        next.act, ccs!{ @{Rc::clone(l)} | @{next.to} }
                    ));
                }
                Ok(set)
            },
            Process::Sequential(l, r) => {
                let mut set = Vec::new();
                for next in l._get_transitions(program, seen)? {
                    if let Action::Delta = next.act {
                        set.push(Transition::new(
                            ccs_act!{ i }, Rc::clone(&r)
                        ));
                    } else {
                        set.push(Transition::new(
                            next.act, ccs!{ @{next.to}; @{Rc::clone(&r)} }
                        ));
                    }
                }
                Ok(set)
            },
            Process::Restrict(p, comp, set) => {
                let mut res = Vec::new();
                for next in p._get_transitions(program, seen)? {
                    if let Some(name) = next.act.observe() {
                        //if comp == false and set contains name, restrict.
                        //if comp == true and set does not contain name, restrict.
                        if *comp != set.contains(name) {
                            continue;
                        }
                    }
                    res.push(Transition::new(
                        next.act, Rc::new(Process::Restrict(next.to, *comp, set.clone()))
                    ));
                }
                Ok(res)
            }
            Process::When(cond, p) => {
                let val = cond.eval()?;
                if let Value::Bool(b) = &val {
                    if *b {
                        p._get_transitions(program, seen)
                    } else {
                        Ok(Vec::new())
                    }
                } else {
                    Err(Error::WhenError(val))
                }
            }
        }
    }

    pub fn subst(this: &Rc<Process>, var: &str, val: &Value) -> Rc<Process> {
        match this.as_ref() {
            Process::Null =>
                Rc::clone(this),
            Process::Term =>
                Rc::clone(this),
            Process::Name(name, args) => {
                let mut args2 = Vec::new();
                let mut new = false;
                for next in args {
                    let next2 = Exp::subst(next, var, val);
                    if !new && !Rc::ptr_eq(&next2, next) {
                        new = true;
                    }
                    args2.push(next2);
                }
                if new {
                    Rc::new(Process::Name(name.clone(), args2))
                } else {
                    Rc::clone(this)
                }
            },
            Process::Prefix(Action::RecvInto(name, None, var2), p) =>
                if var2 == var {
                    Rc::clone(this)
                } else {
                    let p2 = Process::subst(p, var, val);
                    if Rc::ptr_eq(&p2, &p) {
                        Rc::clone(this)
                    } else {
                        ccs!{ @{Action::RecvInto(name.clone(), None, var2.clone())}.@{p2} }
                    }
                },
            Process::Prefix(Action::RecvInto(name, Some(param), var2), p) => {
                let param2 = Exp::subst(param, var, val);
                if var2 == var {
                    if Rc::ptr_eq(&param2, &param) {
                        Rc::clone(this)
                    } else {
                        ccs!{ @{Action::RecvInto(name.clone(), Some(param2), var2.clone())} . @{Rc::clone(p)} }
                    }
                } else {
                    let p2 = Process::subst(p, var, val);
                    if Rc::ptr_eq(&p2, &p) && Rc::ptr_eq(&param2, &param) {
                        Rc::clone(this)
                    } else {
                        ccs!{ @{Action::RecvInto(name.clone(), Some(param2), var2.clone())} . @{p2} }
                    }
                }
            },
            Process::Prefix(act, p) => {
                let act2 = act.subst(var, val);
                let p2 = Process::subst(p, var, val);
                if act2 == *act && Rc::ptr_eq(&p2, &p) {
                    Rc::clone(this)
                } else {
                    ccs!{ @{act2}.@{p2} }
                }
            }
            Process::Choice(l, r) => {
                let l2 = Process::subst(l, var, val);
                let r2 = Process::subst(r, var, val);
                if Rc::ptr_eq(&l2, &l) && Rc::ptr_eq(&r2, &r) {
                    Rc::clone(this)
                } else {
                    ccs!{ @{l2} + @{r2} }
                }
            },
            Process::Parallel(l, r) => {
                let l2 = Process::subst(l, var, val);
                let r2 = Process::subst(r, var, val);
                if Rc::ptr_eq(&l2, &l) && Rc::ptr_eq(&r2, &r) {
                    Rc::clone(this)
                } else {
                    ccs!{ @{l2} | @{r2} }
                }
            },
            Process::Sequential(l, r) => {
                let l2 = Process::subst(l, var, val);
                let r2 = Process::subst(r, var, val);
                if Rc::ptr_eq(&l2, &l) && Rc::ptr_eq(&r2, &r) {
                    Rc::clone(this)
                } else {
                    ccs!{ @{l2}; @{r2} }
                }
            },
            Process::Restrict(p, comp, set) => {
                let p2 = Process::subst(p, var, val);
                if Rc::ptr_eq(&p2, &p) {
                    Rc::clone(this)
                } else {
                    Rc::new(Process::Restrict(p2, *comp, set.clone()))
                }
            }
            Process::When(cond, p) => {
                let cond2 = Exp::subst(cond, var, val);
                let p2 = Process::subst(p, var, val);
                if Rc::ptr_eq(&cond2, &cond) && Rc::ptr_eq(&p2, &p) {
                    Rc::clone(this)
                } else {
                    ccs!{ when (@{cond2}) @{p2} }
                }
            }
        }
    }
}

impl Binding {
    pub fn new(name: String, args: Vec<String>, process: Rc<Process>) -> Binding {
        Binding { name, args, process }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn args(&self) -> &Vec<String> {
        &self.args
    }

    pub fn process(&self) -> &Rc<Process> {
        &self.process
    }

    pub fn instantiate(&self, args: &Vec<Value>) -> Result<Rc<Process>> {
        if args.len() != self.args.len() {
            return Err(Error::ExpProcessArgs(self.name.clone(), self.args.clone(), args.clone()));
        }

        let mut res = Rc::clone(&self.process);
        for (name, arg) in self.args.iter().zip(args.iter()) {
            res = Process::subst(&res, &name, &arg);
        }
        Ok(res)
    }
}

impl Program {
    pub fn new() -> Program {
        Program { bindings: HashMap::new(), process: None }
    }

    pub fn add_binding(&mut self, binding: Binding) {
        self.bindings.insert(binding.name.clone(), binding);
    }

    pub fn binding(&self, name: &str) -> Option<&Binding> {
        self.bindings.get(name)
    }

    pub fn bindings(&self) -> &HashMap<String, Binding> {
        &self.bindings
    }

    pub fn set_process(&mut self, process: Rc<Process>) {
        self.process.replace(process);
    }

    pub fn process(&self) -> Option<Rc<Process>> {
        self.process.clone()
    }
}



impl From<bool> for Exp {
    fn from(b: bool) -> Self {
        Exp::BoolConst(b)
    }
}

impl From<i64> for Exp {
    fn from(n: i64) -> Self {
        Exp::IntConst(n)
    }
}

impl From<&str> for Exp {
    fn from(s: &str) -> Self {
        Exp::StrConst(s.to_string())
    }
}

impl From<String> for Exp {
    fn from(s: String) -> Self {
        Exp::StrConst(s)
    }
}



impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::ExpUnbound(id) =>
                write!(f, "unbound identifier: {}", id),
            Error::ExpUnaryError(op, val) =>
                write!(f, "type error on unary expression: {} {}", op, val),
            Error::ExpBinaryError(op, l, r) =>
                write!(f, "type error on binary expression: {} {} {}", l, op, r),
            Error::ExpProcessArgs(name, args, values) => {
                write!(f, "non matching process arguments: {}[", name)?;
                for (i, next) in args.iter().enumerate() {
                    if i == 0 {
                        write!(f, "{}", next)?;
                    } else {
                        write!(f, ", {}", next)?;
                    }
                }
                if values.is_empty() {
                    write!(f, "] was instantiated without any arguments")
                } else {
                    write!(f, "] was instantiated with ")?;
                    for (i, next) in values.iter().enumerate() {
                        if i == 0 {
                            write!(f, "{}", next)?;
                        } else {
                            write!(f, ", {}", next)?;
                        }
                    }
                    Ok(())
                }
            },
            Error::Unbound(name) =>
                write!(f, "unbound process `{}`", name),
            Error::Unguarded(name) =>
                write!(f, "unguarded recursion in process `{}`", name),
            Error::UnrestrictedInput(var) =>
                write!(f, "unrestricted input variable `{}`", var),
            Error::WhenError(val) =>
                write!(f, "non boolean type on when process: {}", val)
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

impl fmt::Display for Action {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Action::Tau => write!(f, "i"),
            Action::Delta => write!(f, "e"),
            Action::Act(name) => write!(f, "{}", name),
            Action::Snd(name, None, None) => write!(f, "{}!", name),
            Action::Snd(name, None, Some(exp)) => write!(f, "{}!{}", name, exp),
            Action::Snd(name, Some(param), None) => write!(f, "{}({})!", name, param),
            Action::Snd(name, Some(param), Some(exp)) => write!(f, "{}({})!{}", name, param, exp),
            Action::Recv(name, None, None) => write!(f, "{}?", name),
            Action::Recv(name, None, Some(exp)) => write!(f, "{}?({})", name, exp),
            Action::Recv(name, Some(param), None) => write!(f, "{}({})?", name, param),
            Action::Recv(name, Some(param), Some(exp)) => write!(f, "{}({})?({})", name, param, exp),
            Action::RecvInto(name, None, var) => write!(f, "{}?{}", name, var),
            Action::RecvInto(name, Some(param), var) => write!(f, "{}({})?{}", name, param, var),
        }
    }
}

impl fmt::Display for Process {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Process::Null =>
                write!(f, "0"),
            Process::Term =>
                write!(f, "1"),
            Process::Name(name, args) =>
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "{}[", name)?;
                    for (i, next) in args.iter().enumerate() {
                        if i == 0 {
                            write!(f, "{}", next)?;
                        } else {
                            write!(f, ", {}", next)?;
                        }
                    }
                    write!(f, "]")
                },
            Process::Prefix(act, p) =>
                write!(f, "{}.{}", act, p),
            Process::Choice(l, r) =>
                write!(f, "({} + {})", l, r),
            Process::Parallel(l, r) =>
                write!(f, "({} | {})", l, r),
            Process::Sequential(l, r) =>
                write!(f, "({}; {})", l, r),
            Process::Restrict(p, comp, set) => {
                write!(f, "{}\\{{", p)?;
                if *comp {
                    write!(f, "*")?;
                }
                for (i, next) in set.iter().enumerate() {
                    if !*comp && i == 0 {
                        write!(f, "{}", next)?;
                    } else {
                        write!(f, ", {}", next)?;
                    }
                }
                write!(f, "}}")
            },
            Process::When(cond, p) =>
                write!(f, "when {} {}", cond, p)
        }
    }
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.args.is_empty() {
            write!(f, "{} := {}", self.name, self.process)
        } else {
            write!(f, "{}[", self.name)?;
            for (i, next) in self.args.iter().enumerate() {
                if i == 0 {
                    write!(f, "{}", next)?;
                } else {
                    write!(f, ", {}", next)?;
                }
            }
            write!(f, "] := {}", self.process)
        }
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for next in self.bindings.values() {
            writeln!(f, "{}", next)?;
        }
        if let Some(process) = &self.process {
            write!(f, "\n{}", process)?;
        }
        Ok(())
    }
}

impl fmt::Display for Transition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "--( {} )-> {}", self.act, self.to)
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
