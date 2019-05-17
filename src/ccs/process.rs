use super::*;

use std::collections::{BTreeSet, HashSet};
use std::fmt;
use std::sync::Arc;

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
    When(Exp<ID>, Arc<Process<ID>>),
    InputPoint(Arc<Process<ID>>),
}

impl<ID: Identifier> Process<ID> {
    pub fn get_transitions(
        &self, program: &Program<ID>, fold: &FoldOptions
    ) -> Result<HashSet<Transition<ID>>, ID> {
        let trans = self._get_transitions(program, fold, &mut HashSet::new())?;
        let mut res = HashSet::new();
        for next in trans.into_iter() {
            if let Action::RecvInto(name, _, _) = &next.act {
                return Err(Error::UnrestrictedInput(name.clone()));
            }
            res.insert(next);
        }
        Ok(res)
    }

    fn _get_transitions(
        &self, program: &Program<ID>, fold: &FoldOptions,
        seen: &mut HashSet<ID>
    ) -> Result<Vec<Transition<ID>>, ID> {
        match self {
            Process::Null => {
                Ok(Vec::new())
            },
            Process::Term => {
                Ok(vec![Transition::new(
                    Action::Delta, None, Arc::new(Process::Null)
                )])
            },
            Process::Name(name, args) => {
                if seen.contains(name) {
                    return Err(Error::Unguarded(name.clone()));
                }
                match program.binding(name) {
                    Some(bind) => {
                        let mut values = Vec::new();
                        for next in args {
                            values.push(next.eval()?);
                        }

                        seen.insert(name.clone());
                        let res = bind
                            .instantiate(&values, fold)?
                            ._get_transitions(program, fold, seen)?;
                        seen.remove(name);
                        Ok(res)
                    },
                    None =>
                        Err(Error::Unbound(name.clone()))
                }
            },
            Process::Prefix(act @ Action::RecvInto(_, _, _), p) => {
                Ok(vec![Transition::new(
                    act.eval()?, None, Arc::new(Process::InputPoint(Arc::clone(p)))
                )])
            },
            Process::Prefix(act, p) => {
                Ok(vec![Transition::new(
                    act.eval()?, None, Arc::clone(p)
                )])
            },
            Process::Choice(l, r) => {
                let mut set = l._get_transitions(program, fold, seen)?;
                for next in r._get_transitions(program, fold, seen)? {
                    set.push(next);
                }
                Ok(set)
            },
            Process::Parallel(l, r) => {
                let mut set = Vec::new();
                let trans_l = l._get_transitions(program, fold, seen)?;
                let trans_r = r._get_transitions(program, fold, seen)?;

                let mut lookup = HashMap::new();
                let lookup_left = trans_l.len() <= trans_r.len();
                let it = if lookup_left { trans_l.iter() } else { trans_r.iter() };
                for l in it {
                    if let Action::Tau = &l.act {
                        continue;
                    }
                    lookup.entry(l.act.observe())
                        .or_insert_with(|| Vec::new())
                        .push(l);
                }

                let mut sync = |l: &Transition<ID>, r: &Transition<ID>| {
                    if let (Action::Delta, Action::Delta) = (&l.act, &r.act) {
                        set.push(Transition::new(
                            Action::Delta, None, Arc::new(Process::Parallel(
                                Arc::clone(&l.to),
                                Arc::clone(&r.to)
                            ))
                        ));
                    } else {
                        match l.act.sync(&r.act)? {
                            None => {},
                            Some((Side::Left, None)) => {
                                set.push(Transition::new(
                                    Action::Tau, Some(r.act.clone()), Arc::new(Process::Parallel(
                                        Arc::clone(&l.to),
                                        Arc::clone(&r.to)
                                    ))
                                ));
                            },
                            Some((Side::Right, None)) => {
                                set.push(Transition::new(
                                    Action::Tau, Some(l.act.clone()), Arc::new(Process::Parallel(
                                        Arc::clone(&l.to),
                                        Arc::clone(&r.to)
                                    ))
                                ));
                            },
                            Some((Side::Left, Some((var, val)))) => {
                                set.push(Transition::new(
                                    Action::Tau, Some(r.act.clone()), Arc::new(Process::Parallel(
                                        Process::subst_input(&l.to, &var, &val, fold),
                                        Arc::clone(&r.to)
                                    ))
                                ));
                            },
                            Some((Side::Right, Some((var, val)))) => {
                                set.push(Transition::new(
                                    Action::Tau, Some(l.act.clone()), Arc::new(Process::Parallel(
                                        Arc::clone(&l.to),
                                        Process::subst_input(&r.to, &var, &val, fold),
                                    ))
                                ));
                            }
                        }
                    }
                    Ok(())
                };

                if lookup_left {
                    for r in trans_r.iter() {
                        if let Action::Tau = &r.act {
                            continue;
                        }
                        if let Some(ls) = lookup.get(&r.act.observe()) {
                            for l in ls {
                                sync(l, r)?;
                            }
                        }
                    }
                } else {
                    for l in trans_l.iter() {
                        if let Action::Tau = &l.act {
                            continue;
                        }
                        if let Some(rs) = lookup.get(&l.act.observe()) {
                            for r in rs {
                                sync(l, r)?;
                            }
                        }
                    }
                }

                for next in trans_l {
                    if let Action::Delta = &next.act {
                        continue;
                    }
                    set.push(Transition::new(
                        next.act, next.sync, Arc::new(Process::Parallel(
                            next.to, Arc::clone(r)
                        ))
                    ));
                }
                for next in trans_r {
                    if let Action::Delta = &next.act {
                        continue;
                    }
                    set.push(Transition::new(
                        next.act, next.sync, Arc::new(Process::Parallel(
                            Arc::clone(l), next.to
                        ))
                    ));
                }
                Ok(set)
            },
            Process::Sequential(l, r) => {
                let mut set = Vec::new();
                for next in l._get_transitions(program, fold, seen)? {
                    if let Action::Delta = next.act {
                        set.push(Transition::new(
                            Action::Tau, None, Arc::clone(r)
                        ));
                    } else {
                        set.push(Transition::new(
                            next.act, next.sync,
                            Arc::new(Process::Sequential(next.to, Arc::clone(r)))
                        ));
                    }
                }
                Ok(set)
            },
            Process::Restrict(p, comp, set) => {
                let mut res = Vec::new();
                for next in p._get_transitions(program, fold, seen)? {
                    if let Some(name) = next.act.observe() {
                        //if comp == false and set contains name, restrict.
                        //if comp == true and set does not contain name, restrict.
                        if *comp != set.contains(name) {
                            continue;
                        }
                    }
                    res.push(Transition::new(
                        next.act, next.sync,
                        Arc::new(Process::Restrict(next.to, *comp, set.clone()))
                    ));
                }
                Ok(res)
            }
            Process::When(cond, p) => {
                let val = cond.eval()?;
                if let Value::Bool(b) = &val {
                    if *b {
                        p._get_transitions(program, fold, seen)
                    } else {
                        Ok(Vec::new())
                    }
                } else {
                    Err(Error::WhenError(val))
                }
            }
            Process::InputPoint(_) =>
                unreachable!(),
        }
    }

    pub fn subst_input(this: &Arc<Process<ID>>, var: &ID, val: &Value, fold: &FoldOptions) -> Arc<Process<ID>> {
        match this.as_ref() {
            Process::Choice(l, r) =>
                Arc::new(Process::Choice(
                    Process::subst_input(l, var, val, fold),
                    Process::subst_input(r, var, val, fold)
                )),
            Process::Parallel(l, r) =>
                Arc::new(Process::Parallel(
                    Process::subst_input(l, var, val, fold),
                    Process::subst_input(r, var, val, fold)
                )),
            Process::Sequential(l, r) =>
                Arc::new(Process::Sequential(
                    Process::subst_input(l, var, val, fold),
                    Arc::clone(r)
                )),
            Process::Restrict(p, comp, set) =>
                Arc::new(Process::Restrict(
                    Process::subst_input(p, var, val, fold),
                    *comp, set.clone()
                )),
            Process::InputPoint(p) =>
                Arc::new(p.subst(var.clone(), val, fold)),

            Process::Null
          | Process::Term
          | Process::Name(_, _)
          | Process::Prefix(_, _)
          | Process::When(_, _) =>
                Arc::clone(this)
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
                match (act.subst_map_opt(subst, fold), p.subst_map_opt(subst, fold)) {
                    (None, None) =>
                        None,
                    (act2, p2) => {
                        let act2 = act2.map_or_else(|| act.clone(), |act2| act2);
                        let p2 = p2.map_or_else(|| Arc::clone(&p), |p2| Arc::new(p2));
                        Some(Process::Prefix(act2, p2))
                    }
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
            },
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
            },
            Process::InputPoint(_) =>
                unreachable!(),
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
                Process::When(cond.compress(dict), Arc::new(p.compress(dict))),
            Process::InputPoint(_) =>
                unreachable!()
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
                Process::When(Exp::uncompress(cond, dict), Arc::new(Process::uncompress(p, dict))),
            Process::InputPoint(_) =>
                unreachable!()
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
                write!(f, "when {} {}", cond, p),
            Process::InputPoint(p) =>
                write!(f, "?({})", p)
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
                    write!(f, "{}", DisplayCompressed(name, self.1))
                } else {
                    write!(f, "{}[", DisplayCompressed(name, self.1))?;
                    for (i, next) in args.iter().enumerate() {
                        if i == 0 {
                            write!(f, "{}", DisplayCompressed(next, self.1))?;
                        } else {
                            write!(f, ", {}", DisplayCompressed(next, self.1))?;
                        }
                    }
                    write!(f, "]")
                },
            Process::Prefix(act, p) =>
                write!(f, "{}.{}", DisplayCompressed(act, self.1), DisplayCompressed(p.as_ref(), self.1)),
            Process::Choice(l, r) =>
                write!(f, "({} + {})", DisplayCompressed(l.as_ref(), self.1), DisplayCompressed(r.as_ref(), self.1)),
            Process::Parallel(l, r) =>
                write!(f, "({} | {})", DisplayCompressed(l.as_ref(), self.1), DisplayCompressed(r.as_ref(), self.1)),
            Process::Sequential(l, r) =>
                write!(f, "({}; {})", DisplayCompressed(l.as_ref(), self.1), DisplayCompressed(r.as_ref(), self.1)),
            Process::Restrict(p, comp, set) => {
                write!(f, "{}\\{{", DisplayCompressed(p.as_ref(), self.1))?;
                if *comp {
                    write!(f, "*")?;
                }
                for (i, next) in set.iter().enumerate() {
                    if !*comp && i == 0 {
                        write!(f, "{}", DisplayCompressed(next, self.1))?;
                    } else {
                        write!(f, ", {}", DisplayCompressed(next, self.1))?;
                    }
                }
                write!(f, "}}")
            },
            Process::When(cond, p) =>
                write!(f, "when {} {}", DisplayCompressed(cond, self.1), DisplayCompressed(p.as_ref(), self.1)),
            Process::InputPoint(p) =>
                write!(f, "?({})", DisplayCompressed(p.as_ref(), self.1))
        }
    }
}
