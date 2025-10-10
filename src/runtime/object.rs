use std::cell::RefCell;
use std::collections::HashMap;
use std::{fmt, rc::Rc};

use crate::runtime::vm::vm::RuntimeError;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HashKey {
    Integer(i64),
    Boolean(bool),
    String(String),
}

impl fmt::Display for HashKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HashKey::Integer(value) => {
                write!(f, "{}", value)
            }
            HashKey::Boolean(value) => {
                write!(f, "{}", value)
            }
            HashKey::String(value) => {
                write!(f, "{}", value)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Object {
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Builtin(&'static BuiltinFunction),
    CompiledFunction(Rc<CompiledFunction>),
    String(Rc<RefCell<Vec<char>>>),
    Char(char),
    Array(Rc<RefCell<Vec<Object>>>),
    Hash(Rc<RefCell<HashMap<HashKey, Object>>>),
    Closure(Rc<Closure>),
    Cell(ClosureCell),
    Null,
    Void,
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Object::Integer(value) => {
                write!(f, "{}", value)
            }
            Object::Float(value) => {
                write!(f, "{}", value)
            }
            Object::Boolean(value) => {
                write!(f, "{}", value)
            }
            Object::CompiledFunction(value) => {
                write!(f, "CompiledFunction{:?}", value.instructions)
            }
            Object::String(value) => {
                write!(f, "{}", value.borrow().iter().collect::<String>())
            }
            Object::Char(value) => {
                write!(f, "{}", value)
            }
            Object::Builtin(value) => {
                write!(f, "{}", value)
            }
            Object::Array(value) => {
                let elements: Vec<String> = value.borrow().iter().map(|el| el.to_string()).collect();

                write!(f, "[{}]", elements.join(", "))
            }
            Object::Hash(value) => {
                let pairs: Vec<String> =
                    value.borrow().iter().map(|(k, v)| format!("{}: {}", k, v)).collect();
                write!(f, "{{{}}}", pairs.join(", "))
            }
            Object::Closure(value) => {
                write!(f, "{}", value)
            }
            Object::Cell(value) => {
                write!(f, "{}", value.borrow())
            }
            Object::Null => {
                write!(f, "null")
            }
            Object::Void => {
                write!(f, "")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct BuiltinFunction {
    pub name: &'static str,
    pub func: fn(&[Object]) -> Result<Object, RuntimeError>,
}

impl PartialEq for BuiltinFunction {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl fmt::Display for BuiltinFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CompiledFunction {
    pub instructions: Box<[u8]>,
    pub amount_locals: usize,
    pub amount_parameters: usize,
}

impl CompiledFunction {
    pub fn new(instructions: Box<[u8]>, amount_locals: usize, amount_parameters: usize) -> Self {
        CompiledFunction {
            instructions: instructions,
            amount_locals: amount_locals,
            amount_parameters,
        }
    }
}

pub type ClosureCell = Rc<RefCell<Object>>;

#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    pub function: Rc<CompiledFunction>,
    pub free: Box<[Object]>,
}

impl Closure {
    pub fn new(function: Rc<CompiledFunction>, free: Box<[Object]>) -> Self {
        Closure {
            function: function,
            free: free,
        }
    }
}

impl fmt::Display for Closure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Closure{:?}", self.function.instructions)
    }
}
