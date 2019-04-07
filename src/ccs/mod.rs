mod exp;
pub use exp::*;

mod process;
pub use process::*;

use crate::{ccs, ccs_act, ccs_exp};

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

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

#[derive(Clone, Debug)]
pub struct Binding {
    pub(crate) name: String,
    pub(crate) args: Vec<String>,
    pub(crate) process: Arc<Process>
}

#[derive(Clone, Debug, Default)]
pub struct Program {
    pub(crate) bindings: HashMap<String, Binding>,
    pub(crate) process: Option<Arc<Process>>
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Transition {
    pub act: Action,
    pub to: Arc<Process>
}

impl Transition {
    pub fn new(act: Action, to: Arc<Process>) -> Transition {
        Transition { act, to }
    }
}

impl Binding {
    pub fn new(name: String, args: Vec<String>, process: Arc<Process>) -> Binding {
        Binding { name, args, process }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn args(&self) -> &Vec<String> {
        &self.args
    }

    pub fn process(&self) -> &Arc<Process> {
        &self.process
    }

    pub fn instantiate(&self, args: &Vec<Value>) -> Result<Arc<Process>> {
        if args.len() != self.args.len() {
            return Err(Error::ExpProcessArgs(self.name.clone(), self.args.clone(), args.clone()));
        }

        let mut subst = HashMap::new();
        for (name, arg) in self.args.iter().zip(args.iter()) {
            subst.insert(&name[..], arg);
        }
        Ok(Process::subst_map(&self.process, &subst))
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

    pub fn set_process(&mut self, process: Arc<Process>) {
        self.process.replace(process);
    }

    pub fn process(&self) -> Option<Arc<Process>> {
        self.process.clone()
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
