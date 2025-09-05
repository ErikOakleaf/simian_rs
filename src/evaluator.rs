use std::cell::RefCell;
use std::rc::Rc;

use crate::ast::{
    Expression, FunctionLiteralExpression, IdentifierExpression, IfExpression, Program, Statement,
};
use crate::object::{Enviroment, Function, Object};

#[derive(Debug, Clone, PartialEq)]
pub enum EvaluationError {
    TypeMismatch {
        operator: String,
        left: Object,
        right: Object,
    },
    UnknownOperator {
        operator: String,
        left: Option<Object>,
        right: Object,
    },
    UnknownIdentifier(String),
}

pub enum EvaluationResult {
    Value(Object),
    Return(Object),
}

impl EvaluationResult {
    pub fn unwrap_object(self) -> Object {
        match self {
            EvaluationResult::Value(object) => object,
            EvaluationResult::Return(object) => object,
        }
    }
}

pub fn eval_program(
    program: &Program,
    enviroment: &Rc<RefCell<Enviroment>>,
) -> Result<Object, EvaluationError> {
    match eval_statements(&program.statements, enviroment)? {
        EvaluationResult::Value(object) => Ok(object),
        EvaluationResult::Return(object) => Ok(object),
    }
}

fn eval_statements(
    statements: &[Statement],
    enviroment: &Rc<RefCell<Enviroment>>,
) -> Result<EvaluationResult, EvaluationError> {
    let mut result = Object::Null.into_value();
    for statement in statements {
        result = eval_statement(&statement, enviroment)?;

        if let EvaluationResult::Return(_) = result {
            return Ok(result);
        }
    }
    Ok(result)
}

fn eval_statement(
    statement: &Statement,
    enviroment: &Rc<RefCell<Enviroment>>,
) -> Result<EvaluationResult, EvaluationError> {
    match statement {
        Statement::Expression(expression_statement) => {
            eval_expression(expression_statement.expression.as_ref(), enviroment)
        }
        Statement::Return(return_statement) => Ok(eval_expression(
            return_statement.return_value.as_ref(),
            enviroment,
        )?
        .unwrap_object()
        .into_return()),
        Statement::Let(let_statement) => {
            let value = eval_expression(let_statement.value.as_ref(), enviroment)?.unwrap_object();
            let name = let_statement.name.token.literal.clone();
            enviroment.borrow_mut().set(&name, value);
            Ok(Object::Void.into_value())
        }
    }
}

fn eval_expression(
    expression: &Expression,
    enviroment: &Rc<RefCell<Enviroment>>,
) -> Result<EvaluationResult, EvaluationError> {
    let result = match expression {
        Expression::IntegerLiteral(integer_literal_expression) => {
            Object::Integer(integer_literal_expression.value)
        }
        Expression::Boolean(boolean_expression) => Object::Boolean(boolean_expression.value),
        Expression::String(string_expression) => Object::String(string_expression.literal.clone()),
        Expression::Identifier(identifier_expression) => {
            let borrow = enviroment.borrow();
            eval_identifier_expression(identifier_expression, &borrow)?
        }
        Expression::Prefix(prefix_expression) => {
            let right = eval_expression(&prefix_expression.right, enviroment)?.unwrap_object();

            eval_prefix_expression(&prefix_expression.token.literal, &right)?
        }
        Expression::Infix(infix_expression) => {
            let left = eval_expression(&infix_expression.left, enviroment)?.unwrap_object();
            let right = eval_expression(&infix_expression.right, enviroment)?.unwrap_object();

            eval_infix_expression(&infix_expression.token.literal, &left, &right)?
        }
        Expression::If(if_expression) => return eval_if_expression(&if_expression, enviroment),
        Expression::Function(function_expression) => {
            let function = eval_function_expression(function_expression, &enviroment);
            Object::Function(function)
        }
        Expression::Call(call_expression) => {
            let function_object =
                eval_expression(call_expression.function.as_ref(), enviroment)?.unwrap_object();
            let arguments_result: Result<Vec<Object>, EvaluationError> = call_expression
                .arguments
                .iter()
                .map(|arg| eval_expression(arg, enviroment).map(|res| res.unwrap_object()))
                .collect();
            let arguments = arguments_result?;

            match function_object {
                Object::Function(function) => apply_function(&function, arguments)?,
                other => {
                    return Err(EvaluationError::TypeMismatch {
                        operator: "call".to_string(),
                        left: other,
                        right: Object::Null,
                    });
                }
            }
        }
    };

    Ok(result.into_value())
}

fn eval_prefix_expression(operator: &str, right: &Object) -> Result<Object, EvaluationError> {
    match operator {
        "!" => Ok(eval_bang_operator_expression(right)),
        "-" => eval_minus_prefix_operator_expression(right),
        _ => unreachable!("invalid prefix operator passed from parser: {}", operator),
    }
}

fn eval_bang_operator_expression(right: &Object) -> Object {
    match right {
        Object::Boolean(boolean) => Object::Boolean(!boolean),
        Object::Null => Object::Boolean(true),
        _ => Object::Boolean(false),
    }
}

fn eval_minus_prefix_operator_expression(right: &Object) -> Result<Object, EvaluationError> {
    match right {
        Object::Integer(integer) => Ok(Object::Integer(-integer)),
        other => Err(EvaluationError::UnknownOperator {
            operator: "-".to_string(),
            left: None,
            right: other.clone(),
        }),
    }
}

fn eval_infix_expression(
    operator: &str,
    left: &Object,
    right: &Object,
) -> Result<Object, EvaluationError> {
    match (left, right) {
        (Object::Integer(l), Object::Integer(r)) => eval_integer_infix_expression(operator, *l, *r),
        (Object::Boolean(l), Object::Boolean(r)) => eval_bool_infix_expression(operator, *l, *r),
        (Object::String(l), Object::String(r)) => eval_string_infix_expression(operator, l.clone(), r.clone()),
        (l, r) => Err(EvaluationError::TypeMismatch {
            operator: operator.to_string(),
            left: l.clone(),
            right: r.clone(),
        }),
    }
}

fn eval_integer_infix_expression(
    operator: &str,
    l: i64,
    r: i64,
) -> Result<Object, EvaluationError> {
    match operator {
        "+" => Ok(Object::Integer(l + r)),
        "-" => Ok(Object::Integer(l - r)),
        "*" => Ok(Object::Integer(l * r)),
        "/" => Ok(Object::Integer(l / r)),
        ">" => Ok(Object::Boolean(l > r)),
        "<" => Ok(Object::Boolean(l < r)),
        "==" => Ok(Object::Boolean(l == r)),
        "!=" => Ok(Object::Boolean(l != r)),
        other => Err(EvaluationError::UnknownOperator {
            operator: other.to_string(),
            left: Some(Object::Integer(l)),
            right: Object::Integer(r),
        }),
    }
}

fn eval_bool_infix_expression(operator: &str, l: bool, r: bool) -> Result<Object, EvaluationError> {
    match operator {
        "==" => Ok(Object::Boolean(l == r)),
        "!=" => Ok(Object::Boolean(l != r)),
        other => Err(EvaluationError::UnknownOperator {
            operator: other.to_string(),
            left: Some(Object::Boolean(l)),
            right: Object::Boolean(r),
        }),
    }
}

fn eval_string_infix_expression(operator: &str, l: String, r: String) -> Result<Object, EvaluationError> {
    match operator {
        "+" => Ok(Object::String(format!("{}{}", l, r).to_string())),
        other => Err(EvaluationError::UnknownOperator {
            operator: other.to_string(),
            left: Some(Object::String(l)),
            right: Object::String(r),
        }),
    }
}

fn eval_if_expression(
    if_expression: &IfExpression,
    enviroment: &Rc<RefCell<Enviroment>>,
) -> Result<EvaluationResult, EvaluationError> {
    let condition = eval_expression(if_expression.condition.as_ref(), enviroment)?.unwrap_object();

    if is_truthy(&condition) {
        eval_statements(&if_expression.consequence.statements, enviroment)
    } else if let Some(alternative) = &if_expression.alternative {
        eval_statements(&alternative.statements, enviroment)
    } else {
        Ok(EvaluationResult::Value(Object::Null))
    }
}

fn eval_identifier_expression(
    identifier_expression: &IdentifierExpression,
    enviroment: &Enviroment,
) -> Result<Object, EvaluationError> {
    enviroment.get(&identifier_expression.token.literal)
}

fn eval_function_expression(
    function_expression: &FunctionLiteralExpression,
    enviroment: &Rc<RefCell<Enviroment>>,
) -> Function {
    let parameters = function_expression.parameters.clone();
    let body = function_expression.body.clone();
    Function {
        parameters: parameters,
        body: body,
        enviroment: Rc::clone(enviroment),
    }
}

// ----------

fn apply_function(function: &Function, arguments: Vec<Object>) -> Result<Object, EvaluationError> {
    let extended_enviroment = extend_function_enviroment(function, arguments);
    let evaluated = eval_statements(&function.body.statements, &extended_enviroment)?;
    Ok(evaluated.unwrap_object())
}

// Helpers

fn is_truthy(object: &Object) -> bool {
    match object {
        Object::Boolean(boolean) => *boolean,
        Object::Null => false,
        _ => true,
    }
}

fn extend_function_enviroment(
    function: &Function,
    arguments: Vec<Object>,
) -> Rc<RefCell<Enviroment>> {
    let extended_enviroment = Rc::new(RefCell::new(Enviroment::new_enclosed_enviroment(
        Rc::clone(&function.enviroment),
    )));

    for (parameter, argument) in function.parameters.iter().zip(arguments.into_iter()) {
        extended_enviroment
            .borrow_mut()
            .set(&parameter.token.literal, argument);
    }

    extended_enviroment
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::{ParseError, Parser};

    // Test helpers

    fn parse_input(input: &str) -> Result<Program, ParseError> {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        parser.parse_program()
    }

    fn test_eval(input: &str) -> Result<Object, EvaluationError> {
        let program = parse_input(input).expect("Parsing failed");
        let enviroment = Rc::new(RefCell::new(Enviroment::new()));
        eval_program(&program, &enviroment)
    }

    fn test_integer_object(object: Object, expected: i64) {
        if let Object::Integer(integer_object) = object {
            assert_eq!(
                integer_object, expected,
                "value {} is not expected: {}",
                integer_object, expected
            )
        } else {
            panic!("object is not integer object")
        }
    }

    fn test_boolean_object(object: Object, expected: bool) {
        if let Object::Boolean(boolean_object) = object {
            assert_eq!(
                boolean_object, expected,
                "value {} is not expected: {}",
                boolean_object, expected
            )
        } else {
            panic!("object is not boolean object")
        }
    }

    // Tests

    #[test]
    fn test_eval_integer_expression() -> Result<(), EvaluationError> {
        let tests: [(&str, i64); 15] = [
            ("5", 5),
            ("10", 10),
            ("-5", -5),
            ("-10", -10),
            ("5 + 5 + 5 + 5 - 10", 10),
            ("2 * 2 * 2 * 2 * 2", 32),
            ("-50 + 100 + -50", 0),
            ("5 * 2 + 10", 20),
            ("5 + 2 * 10", 25),
            ("20 + 2 * -10", 0),
            ("50 / 2 * 2 + 10", 60),
            ("2 * (5 + 10)", 30),
            ("3 * 3 * 3 + 10", 37),
            ("3 * (3 * 3) + 10", 37),
            ("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input)?;
            test_integer_object(evaluated, expected);
        }

        Ok(())
    }

    #[test]
    fn test_eval_boolean_expression() -> Result<(), String> {
        let tests: [(&str, bool); 19] = [
            ("true", true),
            ("true", true),
            ("1 < 2", true),
            ("1 > 2", false),
            ("1 < 1", false),
            ("1 > 1", false),
            ("1 == 1", true),
            ("1 != 1", false),
            ("1 == 2", false),
            ("1 != 2", true),
            ("true == true", true),
            ("false == false", true),
            ("true == false", false),
            ("true != false", true),
            ("false != true", true),
            ("(1 < 2) == true", true),
            ("(1 < 2) == false", false),
            ("(1 > 2) == true", false),
            ("(1 > 2) == false", true),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input).unwrap();
            test_boolean_object(evaluated, expected);
        }

        Ok(())
    }

    #[test]
    fn test_bang_operator() -> Result<(), String> {
        let tests: [(&str, bool); 8] = [
            ("true", true),
            ("true", true),
            ("!true", false),
            ("!false", true),
            ("!5", false),
            ("!!true", true),
            ("!!false", false),
            ("!!5", true),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input).unwrap();
            test_boolean_object(evaluated, expected);
        }

        Ok(())
    }

    #[test]
    fn test_if_else_expression() -> Result<(), String> {
        let tests: [(&str, Object); 7] = [
            ("if (true) { 10 }", Object::Integer(10)),
            ("if (false) { 10 }", Object::Null),
            ("if (1) { 10 }", Object::Integer(10)),
            ("if (1 < 2) { 10 }", Object::Integer(10)),
            ("if (1 > 2) { 10 }", Object::Null),
            ("if (1 > 2) { 10 } else { 20 }", Object::Integer(20)),
            ("if (1 < 2) { 10 } else { 20 }", Object::Integer(10)),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input).unwrap();
            if let Object::Integer(integer) = expected {
                test_integer_object(evaluated, integer);
            } else {
                assert!(matches!(evaluated, Object::Null), "Object is not Null");
            }
        }

        Ok(())
    }

    #[test]
    fn test_return_statements() -> Result<(), String> {
        let tests: [(&str, i64); 5] = [
            ("return 10;", 10),
            ("return 10; 9;", 10),
            ("return 2 * 5; 9;", 10),
            ("9; return 2 * 5; 9;", 10),
            (
                "
                if (10 > 1) {
                    if (10 > 1) {
                        return 10;
                    }
                    return 1;
                }
",
                10,
            ),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input).unwrap();
            test_integer_object(evaluated, expected);
        }

        Ok(())
    }

    #[test]
    fn test_error_handling() -> Result<(), String> {
        let tests: [(&str, EvaluationError); 9] = [
            (
                "5 + true;",
                EvaluationError::TypeMismatch {
                    operator: "+".to_string(),
                    left: Object::Integer(5),
                    right: Object::Boolean(true),
                },
            ),
            (
                "5 + true; 5;",
                EvaluationError::TypeMismatch {
                    operator: "+".to_string(),
                    left: Object::Integer(5),
                    right: Object::Boolean(true),
                },
            ),
            (
                "-true",
                EvaluationError::UnknownOperator {
                    operator: "-".to_string(),
                    left: None,
                    right: Object::Boolean(true),
                },
            ),
            (
                "true + false;",
                EvaluationError::UnknownOperator {
                    operator: "+".to_string(),
                    left: Some(Object::Boolean(true)),
                    right: Object::Boolean(false),
                },
            ),
            (
                "5; true + false; 5",
                EvaluationError::UnknownOperator {
                    operator: "+".to_string(),
                    left: Some(Object::Boolean(true)),
                    right: Object::Boolean(false),
                },
            ),
            (
                "if (10 > 1) { true + false; }",
                EvaluationError::UnknownOperator {
                    operator: "+".to_string(),
                    left: Some(Object::Boolean(true)),
                    right: Object::Boolean(false),
                },
            ),
            (
                "
                if (10 > 1) {
                if (10 > 1) {
                return true + false;
                }
                return 1;
                }
                ",
                EvaluationError::UnknownOperator {
                    operator: "+".to_string(),
                    left: Some(Object::Boolean(true)),
                    right: Object::Boolean(false),
                },
            ),
            (
                "foobar",
                EvaluationError::UnknownIdentifier("foobar".to_string()),
            ),
            (
                "\"hello\" - \"world\"",
                EvaluationError::UnknownOperator {
                    operator: "-".to_string(),
                    left: Some(Object::String("hello".to_string())),
                    right: Object::String("world".to_string()),
                },
        )
        ];

        for (input, expected) in tests {
            match test_eval(input) {
                Ok(obj) => panic!("expected error but got object instead: {}", obj),
                Err(err) => assert_eq!(err, expected),
            }
        }

        Ok(())
    }

    #[test]
    fn test_let_statements() -> Result<(), String> {
        let tests: [(&str, i64); 4] = [
            ("let a = 5; a;", 5),
            ("let a = 5 * 5; a;", 25),
            ("let a = 5; let b = a; b;", 5),
            ("let a = 5; let b = a; let c = a + b + 5; c;", 15),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input).unwrap();
            test_integer_object(evaluated, expected);
        }

        Ok(())
    }

    #[test]
    fn test_function_object() -> Result<(), String> {
        let input = "fn(x) { x + 2 };";
        let evaluated = test_eval(input).unwrap();

        if let Object::Function(function) = evaluated {
            assert_eq!(
                function.parameters.len(),
                1,
                "function does not have the right amount of parameters got {} expected {}",
                function.parameters.len(),
                1
            );
            assert_eq!(
                format!("{}", function.parameters[0]),
                "x",
                "function does not have the correct parameters got {} expected {}",
                function.parameters[0],
                "x",
            );
            assert_eq!(
                format!("{}", function.body),
                "(x + 2)",
                "function does not have the correct body got {} expected {}",
                function.body,
                "(x + 2)",
            );
        } else {
            panic!("Object is not function object")
        }

        Ok(())
    }

    #[test]
    fn test_function_application() -> Result<(), String> {
        let tests: [(&str, i64); 6] = [
            ("let identity = fn(x) { x; }; identity(5);", 5),
            ("let identity = fn(x) { return x; }; identity(5);", 5),
            ("let double = fn(x) { x * 2; }; double(5);", 10),
            ("let add = fn(x, y) { x + y; }; add(5, 5);", 10),
            ("let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));", 20),
            ("fn(x) { x; }(5)", 5),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input).unwrap();
            test_integer_object(evaluated, expected);
        }

        Ok(())
    }

    #[test]
    fn test_closures() -> Result<(), String> {
        let input = "
            let newAdder = fn(x) {
                fn(y) { x + y };
            };

            let addTwo = newAdder(2);
            addTwo(2);";

        let evaluated = test_eval(input).unwrap();
        test_integer_object(evaluated, 4);

        Ok(())
    }

    #[test]
    fn test_string_literal() -> Result<(), String> {
        let input = "\"hello world\"";

        let evaluated = test_eval(input).unwrap();

        if let Object::String(string) = evaluated {
            assert_eq!(
                string, "hello world",
                "expected \"hell world\" got \"{}\"",
                string
            );
        } else {
            panic!("Object is not string object")
        }

        Ok(())
    }

    #[test]
    fn test_string_concatenation() -> Result<(), String> {
        let input = "\"hello\" + \" \" + \"world\"";

        let evaluated = test_eval(input).unwrap();

        if let Object::String(string) = evaluated {
            assert_eq!(
                string, "hello world",
                "expected \"hell world\" got \"{}\"",
                string
            );
        } else {
            panic!("Object is not string object")
        }

        Ok(())
    }
}
