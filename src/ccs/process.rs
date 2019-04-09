use super::*;

use std::collections::{BTreeSet, HashSet};
use std::fmt;
use std::sync::Arc;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Action<ID: Identifier = String> {
    Tau,
    Delta,
    Act(ID),
    Snd(ID, Option<Exp<ID>>, Option<Exp<ID>>),
    Recv(ID, Option<Exp<ID>>, Option<Exp<ID>>),
    RecvInto(ID, Option<Exp<ID>>, ID)
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Process<ID: Identifier = String> {
    Null,
    Term,
    Name(ID, Vec<Exp<ID>>),
    Prefix(Action<ID>, Arc<Process<ID>>),
    Choice(Arc<Process<ID>>, Arc<Process<ID>>),
    Parallel(Arc<Process<ID>>, Arc<Process<ID>>),
    Sequential(Arc<Process<ID>>, Arc<Process<ID>>),
    Restrict(Arc<Process<ID>>, bool, BTreeSet<ID>), //process, complement, restriction set
    When(Exp<ID>, Arc<Process<ID>>)
}

pub enum Side {
    Left, Right
}

impl<ID: Identifier> Action<ID> {
    pub fn sync(&self, other: &Action<ID>) -> Result<Option<Option<(Side, ID, Value)>>, ID> {
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

    pub fn observe(&self) -> Option<&ID> {
        match self {
            Action::Act(name) | Action::Snd(name, _, _) | Action::Recv(name, _, _) | Action::RecvInto(name, _, _) =>
                Some(name),
            _ =>
                None
        }
    }

    pub fn subst<S>(&self, var: S, val: &Value, fold: &FoldOptions) -> Action<ID>
        where S: Into<ID>
    {
        let mut subst = HashMap::new();
        subst.insert(var.into(), val);
        self.subst_map(&subst, fold)
    }

    pub fn subst_map(&self, subst: &HashMap<ID, &Value>, fold: &FoldOptions) -> Action<ID> {
        match self {
            Action::Tau
          | Action::Delta
          | Action::Act(_)
          | Action::Snd(_, None, None)
          | Action::Recv(_, None, None)
          | Action::RecvInto(_, None, _) =>
                self.clone(),

            Action::Snd(name, None, Some(exp)) =>
                Action::Snd(name.clone(), None, Some(Exp::subst_map(exp, subst, fold))),
            Action::Snd(name, Some(param), None) =>
                Action::Snd(name.clone(), Some(Exp::subst_map(param, subst, fold)), None),
            Action::Snd(name, Some(param), Some(exp)) =>
                Action::Snd(name.clone(), Some(Exp::subst_map(param, subst, fold)), Some(Exp::subst_map(exp, subst, fold))),

            Action::Recv(name, None, Some(exp)) =>
                Action::Recv(name.clone(), None, Some(Exp::subst_map(exp, subst, fold))),
            Action::Recv(name, Some(param), None) =>
                Action::Recv(name.clone(), Some(Exp::subst_map(param, subst, fold)), None),
            Action::Recv(name, Some(param), Some(exp)) =>
                Action::Recv(name.clone(), Some(Exp::subst_map(param, subst, fold)), Some(Exp::subst_map(exp, subst, fold))),

            Action::RecvInto(name, Some(param), var2) =>
                Action::RecvInto(name.clone(), Some(Exp::subst_map(param, subst, fold)), var2.clone()),
        }
    }

    pub fn eval(&self) -> Result<Action<ID>, ID> {
        match self {
            Action::Tau
          | Action::Delta
          | Action::Act(_)
          | Action::Snd(_, None, None)
          | Action::Recv(_, None, None)
          | Action::RecvInto(_, None, _) =>
                Ok(self.clone()),

            Action::Snd(name, None, Some(exp)) =>
                Ok(Action::Snd(name.clone(), None, Some(exp.eval()?.into()))),
            Action::Snd(name, Some(param), None) =>
                Ok(Action::Snd(name.clone(), Some(param.eval()?.into()), None)),
            Action::Snd(name, Some(param), Some(exp)) =>
                Ok(Action::Snd(name.clone(), Some(param.eval()?.into()), Some(exp.eval()?.into()))),

            Action::Recv(name, None, Some(exp)) =>
                Ok(Action::Recv(name.clone(), None, Some(exp.eval()?.into()))),
            Action::Recv(name, Some(param), None) =>
                Ok(Action::Recv(name.clone(), Some(param.eval()?.into()), None)),
            Action::Recv(name, Some(param), Some(exp)) =>
                Ok(Action::Recv(name.clone(), Some(param.eval()?.into()), Some(exp.eval()?.into()))),

            Action::RecvInto(name, Some(param), var) =>
                Ok(Action::RecvInto(name.clone(), Some(param.eval()?.into()), var.clone()))
        }
    }

    pub fn compress(&self, dict: &mut Dict<ID>) -> Action<usize> {
        match self {
            Action::Tau =>
                Action::Tau,
            Action::Delta =>
                Action::Delta,
            Action::Act(id) =>
                Action::Act(dict.lookup_insert(id)),
            Action::Snd(id, param, exp) =>
                Action::Snd(dict.lookup_insert(id),
                    param.as_ref().map(|param| param.compress(dict)),
                    exp.as_ref().map(|exp| exp.compress(dict))
                ),
            Action::Recv(id, param, exp) =>
                Action::Recv(dict.lookup_insert(id),
                    param.as_ref().map(|param| param.compress(dict)),
                    exp.as_ref().map(|exp| exp.compress(dict))
                ),
            Action::RecvInto(id, param, var) =>
                Action::RecvInto(dict.lookup_insert(id),
                    param.as_ref().map(|param| param.compress(dict)),
                    dict.lookup_insert(var)
                )
        }
    }

    pub fn uncompress(other: &Action<usize>, dict: &Dict<ID>) -> Action<ID> {
        match other {
            Action::Tau =>
                Action::Tau,
            Action::Delta =>
                Action::Delta,
            Action::Act(id) =>
                Action::Act(dict.index_to_id(*id).clone()),
            Action::Snd(id, param, exp) =>
                Action::Snd(dict.index_to_id(*id).clone(),
                    param.as_ref().map(|param| Exp::uncompress(param, dict)),
                    exp.as_ref().map(|exp| Exp::uncompress(exp, dict))
                ),
            Action::Recv(id, param, exp) =>
                Action::Recv(dict.index_to_id(*id).clone(),
                    param.as_ref().map(|param| Exp::uncompress(param, dict)),
                    exp.as_ref().map(|exp| Exp::uncompress(exp, dict))
                ),
            Action::RecvInto(id, param, var) =>
                Action::RecvInto(dict.index_to_id(*id).clone(),
                    param.as_ref().map(|param| Exp::uncompress(param, dict)),
                    dict.index_to_id(*var).clone()
                )
        }
    }
}

impl<ID: Identifier> Process<ID> {
    pub fn get_transitions(&self, program: &Program<ID>, fold: &FoldOptions) -> Result<HashSet<Transition<ID>>, ID> {
        let trans = self._get_transitions(program, &mut HashSet::new(), fold)?;
        let mut res = HashSet::new();
        for next in trans.into_iter() {
            if let Action::RecvInto(name, _, _) = &next.act {
                return Err(Error::UnrestrictedInput(name.clone()));
            }
            res.insert(next);
        }
        Ok(res)
    }

    fn _get_transitions(&self, program: &Program<ID>, seen: &mut HashSet<ID>, fold: &FoldOptions) -> Result<Vec<Transition<ID>>, ID> {
        match self {
            Process::Null => {
                Ok(Vec::new())
            },
            Process::Term => {
                let mut set = Vec::new();
                set.push(Transition::new(
                    ccs_act!{ e }, Arc::new(ccs!{ 0 })));
                Ok(set)
            },
            Process::Name(name, args) => {
                if seen.contains(name) {
                    return Err(Error::Unguarded(name.clone()));
                }
                match program.binding(name) {
                    Some(bind) => {
                        //let mut seen = seen.clone();
                        seen.insert(name.clone());
                        let mut values = Vec::new();
                        for next in args {
                            values.push(next.eval()?);
                        }
                        let res = bind.instantiate(&values, fold)?._get_transitions(program, seen, fold)?;
                        seen.remove(name);
                        Ok(res)
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
                for next in l._get_transitions(program, seen, fold)? {
                    set.push(Transition::new(
                        next.act, next.to
                    ));
                }
                for next in r._get_transitions(program, seen, fold)? {
                    set.push(Transition::new(
                        next.act, next.to
                    ));
                }
                Ok(set)
            },
            Process::Parallel(l, r) => {
                let mut set = Vec::new();
                let trans_l = l._get_transitions(program, seen, fold)?;
                let trans_r = r._get_transitions(program, seen, fold)?;
                for l in trans_l.iter() {
                    for r in trans_r.iter() {
                        match l.act.sync(&r.act)? {
                            None => {},
                            Some(None) => {
                                //println!("SYNC: {} ||| {}", l.act, r.act);
                                set.push(Transition::new(
                                    ccs_act!{ i }, Arc::new(Process::Parallel(
                                        Arc::clone(&l.to),
                                        Arc::clone(&r.to)
                                    ))
                                ));
                            },
                            Some(Some((Side::Left, var, val))) => {
                                //println!("SYNC: {} ||| {}", l.act, r.act);
                                set.push(Transition::new(
                                    ccs_act!{ i }, Arc::new(Process::Parallel(
                                        Arc::new(l.to.subst(var.clone(), &val, fold)),
                                        Arc::clone(&r.to)
                                    ))
                                ));
                            },
                            Some(Some((Side::Right, var, val))) => {
                                //println!("SYNC: {} ||| {}", l.act, r.act);
                                set.push(Transition::new(
                                    ccs_act!{ i }, Arc::new(Process::Parallel(
                                        Arc::clone(&l.to),
                                        Arc::new(r.to.subst(var.clone(), &val, fold))
                                    ))
                                ));
                            }
                        }

                        if let (Action::Delta, Action::Delta) = (&l.act, &r.act) {
                            set.push(Transition::new(
                                ccs_act!{ e }, Arc::new(Process::Parallel(
                                    Arc::clone(&l.to),
                                    Arc::clone(&r.to)
                                ))
                            ));
                        }
                    }
                }
                for next in trans_l {
                    if let Action::Delta = &next.act {
                        continue;
                    }
                    set.push(Transition::new(
                        next.act, Arc::new(Process::Parallel(
                            next.to, Arc::clone(r)
                        ))
                    ));
                }
                for next in trans_r {
                    if let Action::Delta = &next.act {
                        continue;
                    }
                    set.push(Transition::new(
                        next.act, Arc::new(Process::Parallel(
                            Arc::clone(l), next.to
                        ))
                    ));
                }
                Ok(set)
            },
            Process::Sequential(l, r) => {
                let mut set = Vec::new();
                for next in l._get_transitions(program, seen, fold)? {
                    if let Action::Delta = next.act {
                        set.push(Transition::new(
                            ccs_act!{ i }, Arc::clone(r)
                        ));
                    } else {
                        set.push(Transition::new(
                            next.act, Arc::new(Process::Sequential(next.to, Arc::clone(r)))
                        ));
                    }
                }
                Ok(set)
            },
            Process::Restrict(p, comp, set) => {
                let mut res = Vec::new();
                for next in p._get_transitions(program, seen, fold)? {
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
                        p._get_transitions(program, seen, fold)
                    } else {
                        Ok(Vec::new())
                    }
                } else {
                    Err(Error::WhenError(val))
                }
            }
        }
    }

    pub fn subst<S>(&self, var: S, val: &Value, fold: &FoldOptions) -> Process<ID>
        where S: Into<ID>
    {
        let mut subst = HashMap::new();
        subst.insert(var.into(), val);
        self.subst_map_opt(&subst, fold).unwrap_or_else(|| self.clone())
    }

    pub fn subst_map(&self, subst: &HashMap<ID, &Value>, fold: &FoldOptions) -> Process<ID> {
        self.subst_map_opt(subst, fold).unwrap_or_else(|| self.clone())
    }

    pub fn subst_opt<S>(&self, var: S, val: &Value, fold: &FoldOptions) -> Option<Process<ID>>
        where S: Into<ID>
    {
        let mut subst = HashMap::new();
        subst.insert(var.into(), val);
        self.subst_map_opt(&subst, fold)
    }

    pub fn subst_map_opt(&self, subst: &HashMap<ID, &Value>, fold: &FoldOptions) -> Option<Process<ID>> {
        if subst.is_empty() {
            return None;
        }

        match self {
            Process::Null =>
                None,
            Process::Term =>
                None,
            Process::Name(name, args) => {
                let mut args2 = Vec::new();
                let mut new = false;
                for next in args {
                    match next.subst_map_opt(subst, fold) {
                        None =>
                            args2.push(next.clone()),
                        Some(next2) => {
                            new = true;
                            args2.push(next2);
                        }
                    }
                }
                if new {
                    Some(Process::Name(name.clone(), args2))
                } else {
                    None
                }
            },
            Process::Prefix(Action::RecvInto(name, None, var), p) => {
                let mut subst2 = subst.clone();
                subst2.remove(var);

                match p.subst_map_opt(&subst2, fold) {
                    None =>
                        None,
                    Some(p2) =>
                        Some(Process::Prefix(
                            Action::RecvInto(name.clone(), None, var.clone()),
                            Arc::new(p2)
                        ))
                }
            },
            Process::Prefix(Action::RecvInto(name, Some(param), var), p) => {
                let mut subst2 = subst.clone();
                subst2.remove(var);

                match (param.subst_map_opt(subst, fold), p.subst_map_opt(&subst2, fold)) {
                    (None, None) =>
                        None,
                    (param2, p2) => {
                        let param2 = param2.map_or_else(|| param.clone(), |exp| exp);
                        let p2 = p2.map_or_else(|| Arc::clone(p), |p| Arc::new(p));
                        Some(Process::Prefix(
                            Action::RecvInto(name.clone(), Some(param2), var.clone()),
                            p2
                        ))
                    }
                }
            },
            Process::Prefix(act, p) => {
                let act2 = act.subst_map(subst, fold);
                match p.subst_map_opt(subst, fold) {
                    None =>
                        if act2 == *act {
                            None
                        } else {
                            Some(Process::Prefix(act2, Arc::clone(p)))
                        },
                    Some(p2) =>
                        Some(Process::Prefix(act2, Arc::new(p2)))
                }
            }
            Process::Choice(l, r) => {
                match (l.subst_map_opt(subst, fold), r.subst_map_opt(subst, fold)) {
                    (None, None) =>
                        None,
                    (l2, r2) => {
                        let l2 = l2.map_or_else(|| Arc::clone(l), |l2| Arc::new(l2));
                        let r2 = r2.map_or_else(|| Arc::clone(r), |r2| Arc::new(r2));
                        Some(Process::Choice(l2, r2))
                    }
                }
            },
            Process::Parallel(l, r) => {
                match (l.subst_map_opt(subst, fold), r.subst_map_opt(subst, fold)) {
                    (None, None) =>
                        None,
                    (l2, r2) => {
                        let l2 = l2.map_or_else(|| Arc::clone(l), |l2| Arc::new(l2));
                        let r2 = r2.map_or_else(|| Arc::clone(r), |r2| Arc::new(r2));
                        Some(Process::Parallel(l2, r2))
                    }
                }
            },
            Process::Sequential(l, r) => {
                match (l.subst_map_opt(subst, fold), r.subst_map_opt(subst, fold)) {
                    (None, None) =>
                        None,
                    (l2, r2) => {
                        let l2 = l2.map_or_else(|| Arc::clone(l), |l2| Arc::new(l2));
                        let r2 = r2.map_or_else(|| Arc::clone(r), |r2| Arc::new(r2));
                        Some(Process::Sequential(l2, r2))
                    }
                }
            },
            Process::Restrict(p, comp, set) => {
                match p.subst_map_opt(subst, fold) {
                    None =>
                        None,
                    Some(p2) =>
                        Some(Process::Restrict(Arc::new(p2), *comp, set.clone()))
                }
            }
            Process::When(cond, p) => {
                match (cond.subst_map_opt(subst, fold), p.subst_map_opt(subst, fold)) {
                    (None, None) =>
                        None,
                    (cond2, p2) => {
                        let cond2 = cond2.map_or_else(|| cond.clone(), |cond2| cond2);
                        let p2 = p2.map_or_else(|| Arc::clone(p), |p2| Arc::new(p2));
                        Some(Process::When(cond2, p2))
                    }
                }
            }
        }
    }

    pub fn compress(&self, dict: &mut Dict<ID>) -> Process<usize> {
        match self {
            Process::Null =>
                Process::Null,
            Process::Term =>
                Process::Term,
            Process::Name(id, args) =>
                Process::Name(dict.lookup_insert(id),
                    args.iter().map(|e| e.compress(dict)).collect()),
            Process::Prefix(act, p) =>
                Process::Prefix(act.compress(dict), Arc::new(p.compress(dict))),
            Process::Choice(l, r) =>
                Process::Choice(Arc::new(l.compress(dict)), Arc::new(r.compress(dict))),
            Process::Parallel(l, r) =>
                Process::Parallel(Arc::new(l.compress(dict)), Arc::new(r.compress(dict))),
            Process::Sequential(l, r) =>
                Process::Sequential(Arc::new(l.compress(dict)), Arc::new(r.compress(dict))),
            Process::Restrict(p, comp, set) =>
                Process::Restrict(Arc::new(p.compress(dict)), *comp,
                    set.iter().map(|id| dict.lookup_insert(id)).collect()),
            Process::When(cond, p) =>
                Process::When(cond.compress(dict), Arc::new(p.compress(dict)))
        }
    }

    pub fn uncompress(other: &Process<usize>, dict: &Dict<ID>) -> Process<ID> {
        match other {
            Process::Null =>
                Process::Null,
            Process::Term =>
                Process::Term,
            Process::Name(id, args) =>
                Process::Name(dict.index_to_id(*id).clone(),
                    args.iter().map(|e| Exp::uncompress(e, dict)).collect()),
            Process::Prefix(act, p) =>
                Process::Prefix(Action::uncompress(act, dict), Arc::new(Process::uncompress(p, dict))),
            Process::Choice(l, r) =>
                Process::Choice(Arc::new(Process::uncompress(l, dict)), Arc::new(Process::uncompress(r, dict))),
            Process::Parallel(l, r) =>
                Process::Parallel(Arc::new(Process::uncompress(l, dict)), Arc::new(Process::uncompress(r, dict))),
            Process::Sequential(l, r) =>
                Process::Sequential(Arc::new(Process::uncompress(l, dict)), Arc::new(Process::uncompress(r, dict))),
            Process::Restrict(p, comp, set) =>
                Process::Restrict(Arc::new(Process::uncompress(p, dict)), *comp,
                    set.iter().map(|id| dict.index_to_id(*id).clone()).collect()),
            Process::When(cond, p) =>
                Process::When(Exp::uncompress(cond, dict), Arc::new(Process::uncompress(p, dict)))
        }
    }
}



impl<ID: Identifier> From<bool> for Exp<ID> {
    fn from(b: bool) -> Self {
        Exp::BoolConst(b)
    }
}

impl<ID: Identifier> From<i64> for Exp<ID> {
    fn from(n: i64) -> Self {
        Exp::IntConst(n)
    }
}

impl<ID: Identifier> From<&str> for Exp<ID> {
    fn from(s: &str) -> Self {
        Exp::StrConst(s.to_string())
    }
}

impl<ID: Identifier> From<String> for Exp<ID> {
    fn from(s: String) -> Self {
        Exp::StrConst(s)
    }
}

impl<ID> fmt::Display for Action<ID>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Action::Tau =>
                write!(f, "i"),
            Action::Delta =>
                write!(f, "e"),
            Action::Act(name) =>
                write!(f, "{}", name),
            Action::Snd(name, None, None) =>
                write!(f, "{}!", name),
            Action::Snd(name, None, Some(exp)) =>
                write!(f, "{}!{}", name, exp),
            Action::Snd(name, Some(param), None) =>
                write!(f, "{}({})!", name, param),
            Action::Snd(name, Some(param), Some(exp)) =>
                write!(f, "{}({})!{}", name, param, exp),
            Action::Recv(name, None, None) =>
                write!(f, "{}?", name),
            Action::Recv(name, None, Some(exp)) =>
                write!(f, "{}?({})", name, exp),
            Action::Recv(name, Some(param), None) =>
                write!(f, "{}({})?", name, param),
            Action::Recv(name, Some(param), Some(exp)) =>
                write!(f, "{}({})?({})", name, param, exp),
            Action::RecvInto(name, None, var) =>
                write!(f, "{}?{}", name, var),
            Action::RecvInto(name, Some(param), var) =>
                write!(f, "{}({})?{}", name, param, var),
        }
    }
}

impl<'a, ID> fmt::Display for DisplayCompressed<'a, ID, Action<usize>>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Action::Tau =>
                write!(f, "i"),
            Action::Delta =>
                write!(f, "e"),
            Action::Act(name) =>
                write!(f, "{}", DisplayCompressed(name, &self.1)),
            Action::Snd(name, None, None) =>
                write!(f, "{}!", DisplayCompressed(name, &self.1)),
            Action::Snd(name, None, Some(exp)) =>
                write!(f, "{}!{}", DisplayCompressed(name, &self.1), exp),
            Action::Snd(name, Some(param), None) =>
                write!(f, "{}({})!", DisplayCompressed(name, &self.1), DisplayCompressed(param, &self.1)),
            Action::Snd(name, Some(param), Some(exp)) =>
                write!(f, "{}({})!{}", DisplayCompressed(name, &self.1), DisplayCompressed(param, &self.1), DisplayCompressed(exp, &self.1)),
            Action::Recv(name, None, None) =>
                write!(f, "{}?", DisplayCompressed(name, &self.1)),
            Action::Recv(name, None, Some(exp)) =>
                write!(f, "{}?({})", DisplayCompressed(name, &self.1), DisplayCompressed(exp, &self.1)),
            Action::Recv(name, Some(param), None) =>
                write!(f, "{}({})?", DisplayCompressed(name, &self.1), DisplayCompressed(param, &self.1)),
            Action::Recv(name, Some(param), Some(exp)) =>
                write!(f, "{}({})?({})", DisplayCompressed(name, &self.1), DisplayCompressed(param, &self.1), DisplayCompressed(exp, &self.1)),
            Action::RecvInto(name, None, var) =>
                write!(f, "{}?{}", DisplayCompressed(name, &self.1), DisplayCompressed(var, &self.1)),
            Action::RecvInto(name, Some(param), var) =>
                write!(f, "{}({})?{}", DisplayCompressed(name, &self.1), DisplayCompressed(param, &self.1), DisplayCompressed(var, &self.1)),
        }
    }
}

impl<ID> fmt::Display for Process<ID>
    where ID: Identifier + fmt::Display
{
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

impl<'a, ID> fmt::Display for DisplayCompressed<'a, ID, Process<usize>>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Process::Null =>
                write!(f, "0"),
            Process::Term =>
                write!(f, "1"),
            Process::Name(name, args) =>
                if args.is_empty() {
                    write!(f, "{}", DisplayCompressed(name, &self.1))
                } else {
                    write!(f, "{}[", DisplayCompressed(name, &self.1))?;
                    for (i, next) in args.iter().enumerate() {
                        if i == 0 {
                            write!(f, "{}", DisplayCompressed(next, &self.1))?;
                        } else {
                            write!(f, ", {}", DisplayCompressed(next, &self.1))?;
                        }
                    }
                    write!(f, "]")
                },
            Process::Prefix(act, p) =>
                write!(f, "{}.{}", DisplayCompressed(act, &self.1), DisplayCompressed(p.as_ref(), &self.1)),
            Process::Choice(l, r) =>
                write!(f, "({} + {})", DisplayCompressed(l.as_ref(), &self.1), DisplayCompressed(r.as_ref(), &self.1)),
            Process::Parallel(l, r) =>
                write!(f, "({} | {})", DisplayCompressed(l.as_ref(), &self.1), DisplayCompressed(r.as_ref(), &self.1)),
            Process::Sequential(l, r) =>
                write!(f, "({}; {})", DisplayCompressed(l.as_ref(), &self.1), DisplayCompressed(r.as_ref(), &self.1)),
            Process::Restrict(p, comp, set) => {
                write!(f, "{}\\{{", DisplayCompressed(p.as_ref(), &self.1))?;
                if *comp {
                    write!(f, "*")?;
                }
                for (i, next) in set.iter().enumerate() {
                    if !*comp && i == 0 {
                        write!(f, "{}", DisplayCompressed(next, &self.1))?;
                    } else {
                        write!(f, ", {}", DisplayCompressed(next, &self.1))?;
                    }
                }
                write!(f, "}}")
            },
            Process::When(cond, p) =>
                write!(f, "when {} {}", DisplayCompressed(cond, &self.1), DisplayCompressed(p.as_ref(), &self.1))
        }
    }
}

impl<'a, ID> fmt::Display for DisplayCompressed<'a, ID, Arc<Process<usize>>>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        DisplayCompressed(self.0.as_ref(), self.1).fmt(f)
    }
}
