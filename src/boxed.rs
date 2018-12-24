use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::rc::Rc;
use crate::{UnaryOp, BinaryOp};

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Exp {
    BoolConst(bool),
    IntConst(i64),
    StrConst(String),
    IdExp(String),
    Unary(UnaryOp, Box<Exp>),
    Binary(BinaryOp, Box<Exp>, Box<Exp>)
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Action {
    Tau,
    Delta,
    Act(String),
    Snd(String, Option<Box<Exp>>, Option<Box<Exp>>),
    Recv(String, Option<Box<Exp>>, Option<Box<Exp>>),
    RecvInto(String, Option<Box<Exp>>, String)
}

#[derive(Clone, Debug)]
pub enum Process {
    Null,
    Term,
    Name(String, Vec<Box<Exp>>),
    Prefix(Action, Box<Process>),
    Choice(Box<Process>, Box<Process>),
    Parallel(Box<Process>, Box<Process>),
    Sequential(Box<Process>, Box<Process>),
    Restrict(Box<Process>, bool, BTreeSet<String>), //process, complement, restriction set
    When(Box<Exp>, Box<Process>)
}

#[derive(Clone, Debug)]
pub struct Binding {
    name: String,
    args: Vec<String>,
    process: Box<Process>
}

#[derive(Clone, Debug, Default)]
pub struct Program {
    bindings: HashMap<String, Binding>,
    process: Option<Box<Process>>
}

impl Binding {
    pub fn new(name: String, args: Vec<String>, process: Box<Process>) -> Binding {
        Binding { name, args, process }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn args(&self) -> &Vec<String> {
        &self.args
    }

    pub fn process(&self) -> &Box<Process> {
        &self.process
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

    pub fn set_process(&mut self, process: Box<Process>) {
        self.process.replace(process);
    }

    pub fn process(&self) -> Option<Box<Process>> {
        self.process.clone()
    }
}



impl<'a> From<&'a crate::Exp> for Exp {
    fn from(act: &'a crate::Exp) -> Self {
        match act {
            crate::Exp::BoolConst(b) => Exp::BoolConst(*b),
            crate::Exp::IntConst(n) => Exp::IntConst(*n),
            crate::Exp::StrConst(s) => Exp::StrConst(s.clone()),
            crate::Exp::IdExp(id) => Exp::IdExp(id.clone()),
            crate::Exp::Unary(op, exp) =>
                Exp::Unary(*op, Box::new(exp.as_ref().into())),
            crate::Exp::Binary(op, l, r) =>
                Exp::Binary(*op, Box::new(l.as_ref().into()), Box::new(r.as_ref().into())),
        }
    }
}

impl<'a> From<&'a Rc<crate::Exp>> for Exp {
    fn from(act: &'a Rc<crate::Exp>) -> Self {
        Self::from(act.as_ref())
    }
}

impl<'a> From<&'a crate::Action> for Action {
    fn from(act: &'a crate::Action) -> Self {
        match act {
            crate::Action::Tau => Action::Tau,
            crate::Action::Delta => Action::Delta,
            crate::Action::Act(s) => Action::Act(s.clone()),
            crate::Action::Snd(s, param, exp) =>
                Action::Snd(s.clone(), param.as_ref().map(|p| Box::new(p.as_ref().into())), exp.as_ref().map(|p| Box::new(p.as_ref().into()))),
            crate::Action::Recv(s, param, exp) =>
                Action::Recv(s.clone(), param.as_ref().map(|p| Box::new(p.as_ref().into())), exp.as_ref().map(|p| Box::new(p.as_ref().into()))),
            crate::Action::RecvInto(s, param, var) =>
                Action::RecvInto(s.clone(), param.as_ref().map(|p| Box::new(p.as_ref().into())), var.clone())
        }
    }
}

impl<'a> From<&'a crate::Process> for Process {
    fn from(act: &'a crate::Process) -> Self {
        match act {
            crate::Process::Null => Process::Null,
            crate::Process::Term => Process::Term,
            crate::Process::Name(s, args) =>
                Process::Name(s.clone(), args.iter().map(|a| Box::new(a.as_ref().into())).collect()),
            crate::Process::Prefix(act, p) =>
                Process::Prefix(act.into(), Box::new(p.into())),
            crate::Process::Choice(l, r) =>
                Process::Choice(Box::new(l.into()), Box::new(r.into())),
            crate::Process::Parallel(l, r) =>
                Process::Parallel(Box::new(l.into()), Box::new(r.into())),
            crate::Process::Sequential(l, r) =>
                Process::Sequential(Box::new(l.into()), Box::new(r.into())),
            crate::Process::Restrict(p, comp, set) =>
                Process::Restrict(Box::new(p.into()), *comp, set.clone()),
            crate::Process::When(cond, p) =>
                Process::When(Box::new(cond.into()), Box::new(p.into()))
        }
    }
}

impl<'a> From<&'a Rc<crate::Process>> for Process {
    fn from(act: &'a Rc<crate::Process>) -> Self {
        Self::from(act.as_ref())
    }
}

impl<'a> From<&'a crate::Binding> for Binding {
    fn from(bind: &'a crate::Binding) -> Self {
        Self::new(bind.name.clone(), bind.args.clone(), Box::new((&bind.process).into()))
    }
}

impl<'a> From<&'a crate::Program> for Program {
    fn from(prog: &'a crate::Program) -> Self {
        let mut res = Self::new();
        for next in prog.bindings.values() {
            res.add_binding(next.into());
        }
        if let Some(p) = &prog.process {
            res.set_process(Box::new(p.into()));
        }
        res
    }
}



impl<'a> From<&'a Exp> for crate::Exp {
    fn from(act: &'a Exp) -> Self {
        match act {
            Exp::BoolConst(b) => crate::Exp::BoolConst(*b),
            Exp::IntConst(n) => crate::Exp::IntConst(*n),
            Exp::IdExp(id) => crate::Exp::IdExp(id.clone()),
            Exp::StrConst(s) => crate::Exp::StrConst(s.clone()),
            Exp::Unary(op, exp) =>
                crate::Exp::Unary(*op, Rc::new(exp.as_ref().into())),
            Exp::Binary(op, l, r) =>
                crate::Exp::Binary(*op, Rc::new(l.as_ref().into()), Rc::new(r.as_ref().into())),
        }
    }
}

impl<'a> From<&'a Box<Exp>> for crate::Exp {
    fn from(act: &'a Box<Exp>) -> Self {
        Self::from(act.as_ref())
    }
}

impl<'a> From<&'a Action> for crate::Action {
    fn from(act: &'a Action) -> Self {
        match act {
            Action::Tau => crate::Action::Tau,
            Action::Delta => crate::Action::Delta,
            Action::Act(s) => crate::Action::Act(s.clone()),
            Action::Snd(s, param, exp) =>
                crate::Action::Snd(s.clone(), param.as_ref().map(|p| Rc::new(p.as_ref().into())), exp.as_ref().map(|p| Rc::new(p.as_ref().into()))),
            Action::Recv(s, param, exp) =>
                crate::Action::Recv(s.clone(), param.as_ref().map(|p| Rc::new(p.as_ref().into())), exp.as_ref().map(|p| Rc::new(p.as_ref().into()))),
            Action::RecvInto(s, param, var) =>
                crate::Action::RecvInto(s.clone(), param.as_ref().map(|p| Rc::new(p.as_ref().into())), var.clone())
        }
    }
}

impl<'a> From<&'a Process> for crate::Process {
    fn from(act: &'a Process) -> Self {
        match act {
            Process::Null => crate::Process::Null,
            Process::Term => crate::Process::Term,
            Process::Name(s, args) =>
                crate::Process::Name(s.clone(), args.iter().map(|a| Rc::new(a.as_ref().into())).collect()),
            Process::Prefix(act, p) =>
                crate::Process::Prefix(act.into(), Rc::new(p.into())),
            Process::Choice(l, r) =>
                crate::Process::Choice(Rc::new(l.into()), Rc::new(r.into())),
            Process::Parallel(l, r) =>
                crate::Process::Parallel(Rc::new(l.into()), Rc::new(r.into())),
            Process::Sequential(l, r) =>
                crate::Process::Sequential(Rc::new(l.into()), Rc::new(r.into())),
            Process::Restrict(p, comp, set) =>
                crate::Process::Restrict(Rc::new(p.into()), *comp, set.clone()),
            Process::When(cond, p) =>
                crate::Process::When(Rc::new(cond.into()), Rc::new(p.into()))
        }
    }
}

impl<'a> From<&'a Box<Process>> for crate::Process {
    fn from(act: &'a Box<Process>) -> Self {
        Self::from(act.as_ref())
    }
}

impl<'a> From<&'a Binding> for crate::Binding {
    fn from(bind: &'a Binding) -> Self {
        Self::new(bind.name.clone(), bind.args.clone(), Rc::new((&bind.process).into()))
    }
}

impl<'a> From<&'a Program> for crate::Program {
    fn from(prog: &'a Program) -> Self {
        let mut res = Self::new();
        for next in prog.bindings.values() {
            res.add_binding(next.into());
        }
        if let Some(p) = &prog.process {
            res.set_process(Rc::new(p.into()));
        }
        res
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
