use std::cell::RefCell;
use std::collections::HashMap;
use std::{fmt, rc::Rc};

use crate::runtime::vm::vm::RuntimeError;
use crate::{
    frontend::{BlockStatement, IdentifierExpression},
    runtime::evaluator::{EvaluationError, EvaluationResult},
};

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
    Boolean(bool),
    Function(Function),
    Builtin(&'static BuiltinFunction),
    CompiledFunction(CompiledFunction),
    String(String),
    Array(Vec<Object>),
    Hash(HashMap<HashKey, Object>),
    Null,
    Void,
}

impl Object {
    pub fn into_value(self) -> EvaluationResult {
        EvaluationResult::Value(self)
    }

    pub fn into_return(self) -> EvaluationResult {
        EvaluationResult::Return(self)
    }

    pub fn into_hash_key(&self) -> Result<HashKey, EvaluationError> {
        match self {
            Object::Integer(value) => Ok(HashKey::Integer(value.clone())),
            Object::Boolean(value) => Ok(HashKey::Boolean(value.clone())),
            Object::String(value) => Ok(HashKey::String(value.clone())),
            other => Err(EvaluationError::Other(format!(
                "Object type cannot be a hash key: {}",
                other
            ))),
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Object::Integer(value) => {
                write!(f, "{}", value)
            }
            Object::Boolean(value) => {
                write!(f, "{}", value)
            }
            Object::Function(value) => {
                write!(f, "{}", value)
            }
            Object::CompiledFunction(value) => {
                write!(f, "CompiledFunction{:?}", value.instructions)
            }
            Object::String(value) => {
                write!(f, "{}", value)
            }
            Object::Builtin(value) => {
                write!(f, "{}", value)
            }
            Object::Array(value) => {
                let elements: Vec<String> = value.iter().map(|el| el.to_string()).collect();

                write!(f, "[{}]", elements.join(", "))
            }
            Object::Hash(value) => {
                let pairs: Vec<String> =
                    value.iter().map(|(k, v)| format!("{}: {}", k, v)).collect();
                write!(f, "{{{}}}", pairs.join(", "))
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

#[derive(Debug, Clone, PartialEq)]
pub struct Enviroment {
    store: HashMap<String, Object>,
    outer: Option<Rc<RefCell<Enviroment>>>,
}

impl Enviroment {
    pub fn new() -> Self {
        Enviroment {
            store: HashMap::<String, Object>::new(),
            outer: None,
        }
    }

    pub fn new_enclosed_enviroment(outer: Rc<RefCell<Enviroment>>) -> Self {
        Enviroment {
            store: HashMap::<String, Object>::new(),
            outer: Some(outer),
        }
    }

    pub fn get(&self, name: &str) -> Option<Object> {
        if let Some(object) = self.store.get(name) {
            return Some(object.clone());
        }

        if let Some(outer) = &self.outer {
            return outer.borrow().get(name);
        }

        None
    }

    pub fn set(&mut self, name: &str, object: Object) {
        self.store.insert(name.to_string(), object);
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    pub parameters: Vec<IdentifierExpression>,
    pub body: BlockStatement,
    pub enviroment: Rc<RefCell<Enviroment>>,
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        self.parameters == other.parameters && self.body == other.body
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params: Vec<String> = self.parameters.iter().map(|p| p.to_string()).collect();

        write!(f, "fn({}) {{\n{}\n}}", params.join(", "), self.body)
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
        CompiledFunction { instructions: instructions, amount_locals: amount_locals, amount_parameters }
    }
}
