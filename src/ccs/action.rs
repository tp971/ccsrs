use super::*;

use std::fmt;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Action<ID: Identifier = String> {
    Tau,
    Delta,
    Act(ID),
    Snd(ID, Option<Exp<ID>>, Option<Exp<ID>>),
    Recv(ID, Option<Exp<ID>>, Option<Exp<ID>>),
    RecvInto(ID, Option<Exp<ID>>, ID)
}

pub enum Side {
    Left, Right
}

impl<ID: Identifier> Action<ID> {
    pub fn sync(&self, other: &Action<ID>) -> Result<Option<(Side, Option<(ID, Value)>)>, ID> {
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
                if let Action::Recv(_, _, _) = self {
                    Ok(Some((Side::Left, None)))
                } else {
                    Ok(Some((Side::Right, None)))
                }
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
                    Ok(Some((Side::Left, Some((var.clone(), exp.eval()?)))))
                } else {
                    Ok(Some((Side::Right, Some((var.clone(), exp.eval()?)))))
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
        self.subst_map_opt(&subst, fold).unwrap_or_else(|| self.clone())
    }

    pub fn subst_map(&self, subst: &HashMap<ID, &Value>, fold: &FoldOptions) -> Action<ID> {
        self.subst_map_opt(subst, fold).unwrap_or_else(|| self.clone())
    }

    pub fn subst_opt<S>(&self, var: S, val: &Value, fold: &FoldOptions) -> Option<Action<ID>>
        where S: Into<ID>
    {
        let mut subst = HashMap::new();
        subst.insert(var.into(), val);
        self.subst_map_opt(&subst, fold)
    }

    pub fn subst_map_opt(&self, subst: &HashMap<ID, &Value>, fold: &FoldOptions) -> Option<Action<ID>> {
        match self {
            Action::Tau
          | Action::Delta
          | Action::Act(_)
          | Action::Snd(_, None, None)
          | Action::Recv(_, None, None)
          | Action::RecvInto(_, None, _) =>
                None,

            Action::Snd(name, None, Some(exp)) =>
                match exp.subst_map_opt(subst, fold) {
                    None =>
                        None,
                    Some(exp2) =>
                        Some(Action::Snd(name.clone(), None, Some(exp2)))
                },
            Action::Snd(name, Some(param), None) =>
                match param.subst_map_opt(subst, fold) {
                    None =>
                        None,
                    Some(param2) =>
                        Some(Action::Snd(name.clone(), Some(param2), None))
                },
            Action::Snd(name, Some(param), Some(exp)) =>
                match (param.subst_map_opt(subst, fold), exp.subst_map_opt(subst, fold)) {
                    (None, None) =>
                        None,
                    (param2, exp2) => {
                        let exp2 = exp2.map_or_else(|| exp.clone(), |exp2| exp2);
                        let param2 = param2.map_or_else(|| param.clone(), |param2| param2);
                        Some(Action::Snd(name.clone(), Some(param2), Some(exp2)))
                    }
                },

            Action::Recv(name, None, Some(exp)) =>
                match exp.subst_map_opt(subst, fold) {
                    None =>
                        None,
                    Some(exp2) =>
                        Some(Action::Recv(name.clone(), None, Some(exp2)))
                },
            Action::Recv(name, Some(param), None) =>
                match param.subst_map_opt(subst, fold) {
                    None =>
                        None,
                    Some(param2) =>
                        Some(Action::Recv(name.clone(), Some(param2), None))
                },
            Action::Recv(name, Some(param), Some(exp)) =>
                match (param.subst_map_opt(subst, fold), exp.subst_map_opt(subst, fold)) {
                    (None, None) =>
                        None,
                    (param2, exp2) => {
                        let exp2 = exp2.map_or_else(|| exp.clone(), |exp2| exp2);
                        let param2 = param2.map_or_else(|| param.clone(), |param2| param2);
                        Some(Action::Recv(name.clone(), Some(param2), Some(exp2)))
                    }
                },

            Action::RecvInto(name, Some(param), var2) =>
                match param.subst_map_opt(subst, fold) {
                    None =>
                        None,
                    Some(param2) =>
                        Some(Action::RecvInto(name.clone(), Some(param2), var2.clone()))
                }
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
                write!(f, "{}", DisplayCompressed(name, self.1)),
            Action::Snd(name, None, None) =>
                write!(f, "{}!", DisplayCompressed(name, self.1)),
            Action::Snd(name, None, Some(exp)) =>
                write!(f, "{}!{}", DisplayCompressed(name, self.1), DisplayCompressed(exp, self.1)),
            Action::Snd(name, Some(param), None) =>
                write!(f, "{}({})!", DisplayCompressed(name, self.1), DisplayCompressed(param, self.1)),
            Action::Snd(name, Some(param), Some(exp)) =>
                write!(f, "{}({})!{}", DisplayCompressed(name, self.1), DisplayCompressed(param, self.1), DisplayCompressed(exp, self.1)),
            Action::Recv(name, None, None) =>
                write!(f, "{}?", DisplayCompressed(name, self.1)),
            Action::Recv(name, None, Some(exp)) =>
                write!(f, "{}?({})", DisplayCompressed(name, self.1), DisplayCompressed(exp, self.1)),
            Action::Recv(name, Some(param), None) =>
                write!(f, "{}({})?", DisplayCompressed(name, self.1), DisplayCompressed(param, self.1)),
            Action::Recv(name, Some(param), Some(exp)) =>
                write!(f, "{}({})?({})", DisplayCompressed(name, self.1), DisplayCompressed(param, self.1), DisplayCompressed(exp, self.1)),
            Action::RecvInto(name, None, var) =>
                write!(f, "{}?{}", DisplayCompressed(name, self.1), DisplayCompressed(var, self.1)),
            Action::RecvInto(name, Some(param), var) =>
                write!(f, "{}({})?{}", DisplayCompressed(name, self.1), DisplayCompressed(param, self.1), DisplayCompressed(var, self.1)),
        }
    }
}
