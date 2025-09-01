use std::fmt;
use std::collections::HashMap;

use crate::evaluator::{EvaluationError, EvaluationResult};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    Null,
}

impl Object {
    pub fn into_value(self) -> EvaluationResult {
        EvaluationResult::Value(self)
    }

    pub fn into_return(self) -> EvaluationResult {
        EvaluationResult::Return(self)
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
            Object::Null => {
                write!(f, "null")
            }
        }
    }
}

pub struct Enviroment {
    store: HashMap<String, Object>,
}

impl Enviroment {
    pub fn new() -> Self {
        Enviroment{ store: HashMap::<String, Object>::new() }
    }

    pub fn get(&self, name: &str) -> Result<Object, EvaluationError> {
        self.store.get(name).cloned().ok_or(EvaluationError::UnknownIdentifier(name.to_string()))
    }

    pub fn set(&mut self, name: &str, object: Object) {
        self.store.insert(name.to_string(), object);
    }
}
