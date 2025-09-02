use std::cell::RefCell;
use std::collections::HashMap;
use std::{fmt, rc::Rc};

use crate::{
    ast::{BlockStatement, IdentifierExpression},
    evaluator::{EvaluationError, EvaluationResult},
};

#[derive(Debug, Clone, PartialEq)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    Function(Function),
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
            Object::Function(value) => {
                write!(f, "{}", value)
            }
            Object::Null => {
                write!(f, "null")
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

    pub fn get(&self, name: &str) -> Result<Object, EvaluationError> {
        if let Some(object) = self.store.get(name) {
            return Ok(object.clone());
        }

        if let Some(outer) = &self.outer {
            return outer.borrow().get(name);
        }

        Err(EvaluationError::UnknownIdentifier(name.to_string()))
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
        // Only compare parameters and body, ignore environment
        self.parameters == other.parameters && self.body == other.body
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params: Vec<String> = self.parameters.iter().map(|p| p.to_string()).collect();

        write!(f, "fn({}) {{\n{}\n}}", params.join(", "), self.body)
    }
}
