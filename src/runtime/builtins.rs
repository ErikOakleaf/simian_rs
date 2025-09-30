use std::{cell::RefCell, rc::Rc};

use crate::runtime::{Object, object::BuiltinFunction, vm::vm::RuntimeError};

pub static BUILTINS: &[BuiltinFunction] = &[
    BuiltinFunction {
        name: "len",
        func: len_builtin,
    },
    BuiltinFunction {
        name: "puts",
        func: puts_builtin,
    },
    BuiltinFunction {
        name: "first",
        func: first_builtin,
    },
    BuiltinFunction {
        name: "last",
        func: last_builtin,
    },
    BuiltinFunction {
        name: "rest",
        func: rest_builtin,
    },
    BuiltinFunction {
        name: "push",
        func: push_builtin,
    },
];

fn len_builtin(args: &[Object]) -> Result<Object, RuntimeError> {
    check_args_length(args.len(), 1)?;

    let object = &args[0];

    match object {
        Object::String(string) => Ok(Object::Integer(string.borrow().len() as i64)),
        Object::Array(array) => Ok(Object::Integer(array.borrow().len() as i64)),
        other => Err(RuntimeError::Other(format!(
            "argument to len not supported, got {}",
            other
        ))),
    }
}

fn first_builtin(args: &[Object]) -> Result<Object, RuntimeError> {
    check_args_length(args.len(), 1)?;

    let arr_object = &args[0];
    if let Object::Array(arr) = arr_object {
        if arr.borrow().len() == 0 {
            return Ok(Object::Null);
        }
        Ok(arr.borrow()[0].clone())
    } else {
        Err(RuntimeError::Other(format!(
            "argument to first not supported, got {}",
            arr_object
        )))
    }
}

fn last_builtin(args: &[Object]) -> Result<Object, RuntimeError> {
    check_args_length(args.len(), 1)?;

    let arr_object = &args[0];
    if let Object::Array(arr) = arr_object {
        if arr.borrow().len() == 0 {
            return Ok(Object::Null);
        }
        Ok(arr.borrow().last().unwrap().clone())
    } else {
        Err(RuntimeError::Other(format!(
            "argument to last not supported, got {}",
            arr_object
        )))
    }
}

fn rest_builtin(args: &[Object]) -> Result<Object, RuntimeError> {
    check_args_length(args.len(), 1)?;

    let arr_object = &args[0];
    if let Object::Array(arr) = arr_object {
        if arr.borrow().len() < 1 {
            return Ok(Object::Null);
        }

        if arr.borrow().len() == 1 {
            return Ok(Object::Array(Rc::new(RefCell::new(vec![]))));
        }

        Ok(Object::Array(Rc::new(RefCell::new(arr.borrow()[1..arr.borrow().len()].to_vec()))))
    } else {
        Err(RuntimeError::Other(format!(
            "argument to rest not supported, got {}",
            arr_object
        )))
    }
}

fn push_builtin(args: &[Object]) -> Result<Object, RuntimeError> {
    check_args_length(args.len(), 2)?;

    
if let Object::Array(arr_rc) = &args[0] {
        let arr_borrow = arr_rc.borrow();

        let mut new_vec = arr_borrow.clone();

        new_vec.push(args[1].clone());

        Ok(Object::Array(Rc::new(RefCell::new(new_vec))))
    } else {
        Err(RuntimeError::Other(format!(
            "argument to push not supported, got {}",
            args[0]
        )))
    }
}

fn puts_builtin(args: &[Object]) -> Result<Object, RuntimeError> {
    for object in args {
        println!("{}", object);
    }

    Ok(Object::Void)
}

// Builtin helpers

fn check_args_length(args_length: usize, expected: usize) -> Result<(), RuntimeError> {
    if args_length != expected {
        return Err(RuntimeError::Other(format!(
            "wrong number of arguments. got: {}, expected: {}",
            args_length, expected
        )));
    }

    Ok(())
}
