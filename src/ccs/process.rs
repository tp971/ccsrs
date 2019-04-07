use super::*;

use std::collections::{BTreeSet, HashSet};
use std::fmt;
use std::sync::Arc;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Action {
    Tau,
    Delta,
    Act(String),
    Snd(String, Option<Arc<Exp>>, Option<Arc<Exp>>),
    Recv(String, Option<Arc<Exp>>, Option<Arc<Exp>>),
    RecvInto(String, Option<Arc<Exp>>, String)
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Process {
    Null,
    Term,
    Name(String, Vec<Arc<Exp>>),
    Prefix(Action, Arc<Process>),
    Choice(Arc<Process>, Arc<Process>),
    Parallel(Arc<Process>, Arc<Process>),
    Sequential(Arc<Process>, Arc<Process>),
    Restrict(Arc<Process>, bool, BTreeSet<String>), //process, complement, restriction set
    When(Arc<Exp>, Arc<Process>)
}

pub enum Side {
    Left, Right
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

impl Process {
    pub fn get_transitions(&self, program: &Program) -> Result<HashSet<Transition>> {
        let trans = self._get_transitions(program, HashSet::new())?;
        let mut res = HashSet::new();
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
                    act.eval()?, Arc::clone(p)
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
                                    ccs_act!{ i }, ccs!{ @{Arc::clone(&l.to)} | @{Arc::clone(&r.to)} }
                                ));
                            },
                            Some(Some((Side::Left, var, val))) => {
                                //println!("SYNC: {} ||| {}", l.act, r.act);
                                set.push(Transition::new(
                                    ccs_act!{ i }, ccs!{ @{Process::subst(&l.to, &var, &val)} | @{Arc::clone(&r.to)} }
                                ));
                            },
                            Some(Some((Side::Right, var, val))) => {
                                //println!("SYNC: {} ||| {}", l.act, r.act);
                                set.push(Transition::new(
                                    ccs_act!{ i }, ccs!{ @{Arc::clone(&l.to)} | @{Process::subst(&r.to, &var, &val)} }
                                ));
                            }
                        }

                        if let (Action::Delta, Action::Delta) = (&l.act, &r.act) {
                            set.push(Transition::new(
                                ccs_act!{ e }, ccs!{ @{Arc::clone(&l.to)} | @{Arc::clone(&r.to)} }
                            ));
                        }
                    }
                }
                for next in trans_l {
                    if let Action::Delta = &next.act {
                        continue;
                    }
                    set.push(Transition::new(
                        next.act, ccs!{ @{next.to} | @{Arc::clone(r)} }
                    ));
                }
                for next in trans_r {
                    if let Action::Delta = &next.act {
                        continue;
                    }
                    set.push(Transition::new(
                        next.act, ccs!{ @{Arc::clone(l)} | @{next.to} }
                    ));
                }
                Ok(set)
            },
            Process::Sequential(l, r) => {
                let mut set = Vec::new();
                for next in l._get_transitions(program, seen)? {
                    if let Action::Delta = next.act {
                        set.push(Transition::new(
                            ccs_act!{ i }, Arc::clone(&r)
                        ));
                    } else {
                        set.push(Transition::new(
                            next.act, ccs!{ @{next.to}; @{Arc::clone(&r)} }
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
                        next.act, Arc::new(Process::Restrict(next.to, *comp, set.clone()))
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

    pub fn subst(this: &Arc<Process>, var: &str, val: &Value) -> Arc<Process> {
        match this.as_ref() {
            Process::Null =>
                Arc::clone(this),
            Process::Term =>
                Arc::clone(this),
            Process::Name(name, args) => {
                let mut args2 = Vec::new();
                let mut new = false;
                for next in args {
                    let next2 = Exp::subst(next, var, val);
                    if !new && !Arc::ptr_eq(&next2, next) {
                        new = true;
                    }
                    args2.push(next2);
                }
                if new {
                    Arc::new(Process::Name(name.clone(), args2))
                } else {
                    Arc::clone(this)
                }
            },
            Process::Prefix(Action::RecvInto(name, None, var2), p) =>
                if var2 == var {
                    Arc::clone(this)
                } else {
                    let p2 = Process::subst(p, var, val);
                    if Arc::ptr_eq(&p2, &p) {
                        Arc::clone(this)
                    } else {
                        ccs!{ @{Action::RecvInto(name.clone(), None, var2.clone())}.@{p2} }
                    }
                },
            Process::Prefix(Action::RecvInto(name, Some(param), var2), p) => {
                let param2 = Exp::subst(param, var, val);
                if var2 == var {
                    if Arc::ptr_eq(&param2, &param) {
                        Arc::clone(this)
                    } else {
                        ccs!{ @{Action::RecvInto(name.clone(), Some(param2), var2.clone())} . @{Arc::clone(p)} }
                    }
                } else {
                    let p2 = Process::subst(p, var, val);
                    if Arc::ptr_eq(&p2, &p) && Arc::ptr_eq(&param2, &param) {
                        Arc::clone(this)
                    } else {
                        ccs!{ @{Action::RecvInto(name.clone(), Some(param2), var2.clone())} . @{p2} }
                    }
                }
            },
            Process::Prefix(act, p) => {
                let act2 = act.subst(var, val);
                let p2 = Process::subst(p, var, val);
                if act2 == *act && Arc::ptr_eq(&p2, &p) {
                    Arc::clone(this)
                } else {
                    ccs!{ @{act2}.@{p2} }
                }
            }
            Process::Choice(l, r) => {
                let l2 = Process::subst(l, var, val);
                let r2 = Process::subst(r, var, val);
                if Arc::ptr_eq(&l2, &l) && Arc::ptr_eq(&r2, &r) {
                    Arc::clone(this)
                } else {
                    ccs!{ @{l2} + @{r2} }
                }
            },
            Process::Parallel(l, r) => {
                let l2 = Process::subst(l, var, val);
                let r2 = Process::subst(r, var, val);
                if Arc::ptr_eq(&l2, &l) && Arc::ptr_eq(&r2, &r) {
                    Arc::clone(this)
                } else {
                    ccs!{ @{l2} | @{r2} }
                }
            },
            Process::Sequential(l, r) => {
                let l2 = Process::subst(l, var, val);
                let r2 = Process::subst(r, var, val);
                if Arc::ptr_eq(&l2, &l) && Arc::ptr_eq(&r2, &r) {
                    Arc::clone(this)
                } else {
                    ccs!{ @{l2}; @{r2} }
                }
            },
            Process::Restrict(p, comp, set) => {
                let p2 = Process::subst(p, var, val);
                if Arc::ptr_eq(&p2, &p) {
                    Arc::clone(this)
                } else {
                    Arc::new(Process::Restrict(p2, *comp, set.clone()))
                }
            }
            Process::When(cond, p) => {
                let cond2 = Exp::subst(cond, var, val);
                let p2 = Process::subst(p, var, val);
                if Arc::ptr_eq(&cond2, &cond) && Arc::ptr_eq(&p2, &p) {
                    Arc::clone(this)
                } else {
                    ccs!{ when (@{cond2}) @{p2} }
                }
            }
        }
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
