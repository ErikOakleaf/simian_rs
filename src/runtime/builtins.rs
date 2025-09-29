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
        Object::String(string) => Ok(Object::Integer(string.len() as i64)),
        Object::Array(array) => Ok(Object::Integer(array.len() as i64)),
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
        if arr.len() == 0 {
            return Ok(Object::Null);
        }
        Ok(arr[0].clone())
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
        if arr.len() == 0 {
            return Ok(Object::Null);
        }
        Ok(arr.last().unwrap().clone())
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
        if arr.len() < 1 {
            return Ok(Object::Null);
        }

        if arr.len() == 1 {
            return Ok(Object::Array(vec![]));
        }

        Ok(Object::Array(arr[1..arr.len()].to_vec()))
    } else {
        Err(RuntimeError::Other(format!(
            "argument to rest not supported, got {}",
            arr_object
        )))
    }
}

fn push_builtin(args: &[Object]) -> Result<Object, RuntimeError> {
    check_args_length(args.len(), 2)?;

    let arr_object = &args[0];
    if let Object::Array(arr) = arr_object {
        let mut arr_copy = arr.clone();
        arr_copy.push(args[1].clone());
        Ok(Object::Array(arr_copy))
    } else {
        Err(RuntimeError::Other(format!(
            "argument to push not supported, got {}",
            arr_object
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
