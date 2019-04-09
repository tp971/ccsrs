mod exp;
pub use exp::*;

mod process;
pub use process::*;

use crate::{ccs, ccs_act};

use std::collections::{HashMap, hash_map::Entry};
use std::fmt;
use std::hash::Hash;
use std::sync::Arc;

pub trait Identifier:
    Clone + PartialEq + Eq + PartialOrd + Ord + Hash
{}

impl<T> Identifier for T
    where T: Clone + PartialEq + Eq + PartialOrd + Ord + Hash
{}

#[derive(Debug, Clone)]
pub struct Dict<ID: Identifier> {
    id_to_index: HashMap<ID, usize>,
    index_to_id: Vec<ID>
}

impl<ID: Identifier> Dict<ID> {
    pub fn new() -> Dict<ID> {
        Dict {
            id_to_index: HashMap::new(),
            index_to_id: Vec::new()
        }
    }

    pub fn lookup_insert(&mut self, id: &ID) -> usize {
        match self.id_to_index.entry(id.clone()) {
            Entry::Occupied(v) => *v.get(),
            Entry::Vacant(v) => {
                let res = self.index_to_id.len();
                self.index_to_id.push(id.clone());
                v.insert(res);
                res
            }
        }
    }

    pub fn lookup(&self, id: &ID) -> Option<usize> {
        self.id_to_index.get(id).cloned()
    }

    pub fn get(&self, i: usize) -> Option<&ID> {
        self.index_to_id.get(i)
    }

    pub fn id_to_index(&self, id: &ID) -> usize {
        *self.id_to_index.get(id).unwrap()
    }

    pub fn index_to_id(&self, i: usize) -> &ID {
        &self.index_to_id[i]
    }
}

#[derive(Debug, Copy, Clone)]
pub struct DisplayCompressed<'a, ID: Identifier, T>(pub &'a T, pub &'a Dict<ID>);



type Result<T, ID> = std::result::Result<T, Error<ID>>;

#[derive(Debug, Clone)]
pub enum Error<ID: Identifier> {
    ExpUnbound(ID),
    ExpUnaryError(UnaryOp, Value),
    ExpBinaryError(BinaryOp, Value, Value),
    ExpProcessArgs(ID, Vec<ID>, Vec<Value>),
    Unbound(ID),
    Unguarded(ID),
    UnrestrictedInput(ID),
    WhenError(Value)
}

#[derive(Debug, Clone)]
pub struct Binding<ID: Identifier = String> {
    pub(crate) name: ID,
    pub(crate) args: Vec<ID>,
    pub(crate) process: Process<ID>
}

#[derive(Debug, Clone, Default)]
pub struct Program<ID: Identifier = String> {
    pub(crate) bindings: HashMap<ID, Binding<ID>>,
    pub(crate) process: Option<Process<ID>>
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Transition<ID: Identifier = String> {
    pub act: Action<ID>,
    pub to: Arc<Process<ID>>
}

pub struct FoldOptions {
    pub fold_exp: bool
}



impl<ID: Identifier> Error<ID> {
    pub fn compress(&self, dict: &mut Dict<ID>) -> Error<usize> {
        match self {
            Error::ExpUnbound(id) =>
                Error::ExpUnbound(dict.lookup_insert(id)),
            Error::ExpUnaryError(op, val) =>
                Error::ExpUnaryError(*op, val.clone()),
            Error::ExpBinaryError(op, l, r) =>
                Error::ExpBinaryError(*op, l.clone(), r.clone()),
            Error::ExpProcessArgs(id, args, vals) =>
                Error::ExpProcessArgs(dict.lookup_insert(id),
                    args.iter().map(|id| dict.lookup_insert(id)).collect(),
                    vals.clone()),
            Error::Unbound(id) =>
                Error::Unbound(dict.lookup_insert(id)),
            Error::Unguarded(id) =>
                Error::Unguarded(dict.lookup_insert(id)),
            Error::UnrestrictedInput(id) =>
                Error::UnrestrictedInput(dict.lookup_insert(id)),
            Error::WhenError(val) =>
                Error::WhenError(val.clone())
        }
    }

    pub fn uncompress(other: &Error<usize>, dict: &Dict<ID>) -> Error<ID> {
        match other {
            Error::ExpUnbound(id) =>
                Error::ExpUnbound(dict.index_to_id(*id).clone()),
            Error::ExpUnaryError(op, val) =>
                Error::ExpUnaryError(*op, val.clone()),
            Error::ExpBinaryError(op, l, r) =>
                Error::ExpBinaryError(*op, l.clone(), r.clone()),
            Error::ExpProcessArgs(id, args, vals) =>
                Error::ExpProcessArgs(dict.index_to_id(*id).clone(),
                    args.iter().map(|id| dict.index_to_id(*id).clone()).collect(),
                    vals.clone()),
            Error::Unbound(id) =>
                Error::Unbound(dict.index_to_id(*id).clone()),
            Error::Unguarded(id) =>
                Error::Unguarded(dict.index_to_id(*id).clone()),
            Error::UnrestrictedInput(id) =>
                Error::UnrestrictedInput(dict.index_to_id(*id).clone()),
            Error::WhenError(val) =>
                Error::WhenError(val.clone())
        }
    }
}

impl<ID: Identifier> Binding<ID> {
    pub fn new(name: ID, args: Vec<ID>, process: Process<ID>) -> Binding<ID> {
        Binding { name, args, process }
    }

    pub fn name(&self) -> &ID {
        &self.name
    }

    pub fn args(&self) -> &[ID] {
        &self.args
    }

    pub fn process(&self) -> &Process<ID> {
        &self.process
    }

    pub fn instantiate(&self, args: &[Value], fold: &FoldOptions) -> Result<Process<ID>, ID> {
        if args.len() != self.args.len() {
            return Err(Error::ExpProcessArgs(self.name.clone(), self.args.clone(), args.to_vec()));
        }

        let mut subst = HashMap::new();
        for (name, arg) in self.args.iter().zip(args.iter()) {
            subst.insert(name.clone(), arg);
        }
        Ok(self.process.subst_map(&subst, fold))
    }

    pub fn compress(&self, dict: &mut Dict<ID>) -> Binding<usize> {
        Binding {
            name: dict.lookup_insert(&self.name),
            args: self.args.iter().map(|id| dict.lookup_insert(id)).collect(),
            process: self.process.compress(dict)
        }
    }

    pub fn uncompress(other: &Binding<usize>, dict: &Dict<ID>) -> Binding<ID> {
        Binding {
            name: dict.index_to_id(other.name).clone(),
            args: other.args.iter()
                .map(|id| dict.index_to_id(*id).clone()).collect(),
            process: Process::uncompress(&other.process, dict)
        }
    }
}

impl<ID: Identifier> Program<ID> {
    pub fn new() -> Program<ID> {
        Program { bindings: HashMap::new(), process: None }
    }

    pub fn add_binding(&mut self, binding: Binding<ID>) {
        self.bindings.insert(binding.name.clone(), binding);
    }

    pub fn binding(&self, name: &ID) -> Option<&Binding<ID>> {
        self.bindings.get(name)
    }

    pub fn bindings(&self) -> &HashMap<ID, Binding<ID>> {
        &self.bindings
    }

    pub fn set_process(&mut self, process: Process<ID>) {
        self.process.replace(process);
    }

    pub fn process(&self) -> Option<Process<ID>> {
        self.process.clone()
    }

    pub fn compress(&self, dict: &mut Dict<ID>) -> Program<usize> {
        Program {
            bindings: self.bindings.iter()
                .map(|(id, bind)|
                    (dict.lookup_insert(id), bind.compress(dict))
                )
                .collect(),
            process: self.process.as_ref().map(|p| p.compress(dict))
        }
    }

    pub fn uncompress(other: &Program<usize>, dict: &Dict<ID>) -> Program<ID> {
        Program {
            bindings: other.bindings.iter()
                .map(|(id, bind)|
                    (dict.index_to_id(*id).clone(), Binding::uncompress(bind, dict))
                )
                .collect(),
            process: other.process.as_ref().map(|p| Process::uncompress(p, dict))
        }
    }
}

impl<ID: Identifier> Transition<ID> {
    pub fn new(act: Action<ID>, to: Arc<Process<ID>>) -> Transition<ID> {
        Transition { act, to }
    }

    pub fn compress(&self, dict: &mut Dict<ID>) -> Transition<usize> {
        Transition {
            act: self.act.compress(dict),
            to: Arc::new(self.to.compress(dict))
        }
    }

    pub fn uncompress(other: &Transition<usize>, dict: &Dict<ID>) -> Transition<ID> {
        Transition {
            act: Action::uncompress(&other.act, dict),
            to: Arc::new(Process::uncompress(&other.to, dict))
        }
    }
}

impl Default for FoldOptions {
    fn default() -> FoldOptions {
        FoldOptions {
            fold_exp: false
        }
    }
}



impl<'a, ID> fmt::Display for DisplayCompressed<'a, ID, usize>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.1.index_to_id(*self.0))
    }
}

impl<ID> fmt::Display for Error<ID>
    where ID: Identifier + fmt::Display
{
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

impl<'a, ID> fmt::Display for DisplayCompressed<'a, ID, Error<usize>>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Error::ExpUnbound(id) =>
                write!(f, "unbound identifier: {}", DisplayCompressed(id, self.1)),
            Error::ExpUnaryError(op, val) =>
                write!(f, "type error on unary expression: {} {}", op, val),
            Error::ExpBinaryError(op, l, r) =>
                write!(f, "type error on binary expression: {} {} {}", l, op, r),
            Error::ExpProcessArgs(name, args, values) => {
                write!(f, "non matching process arguments: {}[", DisplayCompressed(name, self.1))?;
                for (i, next) in args.iter().enumerate() {
                    if i == 0 {
                        write!(f, "{}", DisplayCompressed(next, self.1))?;
                    } else {
                        write!(f, ", {}", DisplayCompressed(next, self.1))?;
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
                write!(f, "unbound process `{}`", DisplayCompressed(name, self.1)),
            Error::Unguarded(name) =>
                write!(f, "unguarded recursion in process `{}`", DisplayCompressed(name, self.1)),
            Error::UnrestrictedInput(var) =>
                write!(f, "unrestricted input variable `{}`", DisplayCompressed(var, self.1)),
            Error::WhenError(val) =>
                write!(f, "non boolean type on when process: {}", val)
        }
    }
}

impl<ID> fmt::Display for Binding<ID>
    where ID: Identifier + fmt::Display
{
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

impl<'a, ID> fmt::Display for DisplayCompressed<'a, ID, Binding<usize>>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0.args.is_empty() {
            write!(f, "{} := {}", DisplayCompressed(&self.0.name, self.1), DisplayCompressed(&self.0.process, self.1))
        } else {
            write!(f, "{}[", DisplayCompressed(&self.0.name, self.1))?;
            for (i, next) in self.0.args.iter().enumerate() {
                if i == 0 {
                    write!(f, "{}", DisplayCompressed(next, self.1))?;
                } else {
                    write!(f, ", {}", DisplayCompressed(next, self.1))?;
                }
            }
            write!(f, "] := {}", DisplayCompressed(&self.0.process, self.1))
        }
    }
}

impl<ID> fmt::Display for Program<ID>
    where ID: Identifier + fmt::Display
{
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

impl<'a, ID> fmt::Display for DisplayCompressed<'a, ID, Program<usize>>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for next in self.0.bindings.values() {
            writeln!(f, "{}", DisplayCompressed(next, self.1))?;
        }
        if let Some(process) = &self.0.process {
            write!(f, "\n{}", DisplayCompressed(process, self.1))?;
        }
        Ok(())
    }
}

impl<ID> fmt::Display for Transition<ID>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "--( {} )-> {}", self.act, self.to)
    }
}

impl<'a, ID> fmt::Display for DisplayCompressed<'a, ID, Transition<usize>>
    where ID: Identifier + fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "--( {} )-> {}", DisplayCompressed(&self.0.act, self.1), DisplayCompressed(&self.0.to, self.1))
    }
}
