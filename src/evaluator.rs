use crate::ast::{Expression, IfExpression, PrefixExpression, Program, Statement};
use crate::lexer::Lexer;
use crate::object::Object;
use crate::parser::{ParseError, Parser};

#[derive(Debug, PartialEq, Eq)]
pub enum EvaluationError {
    TypeMismatch {
        operator: String,
        left: Object,
        right: Object,
    },
    UnkownOperator {
        operator: String,
        left: Option<Object>,
        right: Object,
    },
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

pub fn eval_program(program: &Program) -> Result<Object, EvaluationError> {
    match eval_statements(&program.statements)? {
        EvaluationResult::Value(object) => Ok(object),
        EvaluationResult::Return(object) => Ok(object),
    }
}

fn eval_statements(statements: &[Statement]) -> Result<EvaluationResult, EvaluationError> {
    let mut result = Object::Null.into_value();
    for statement in statements {
        result = eval_statement(&statement)?;

        if let EvaluationResult::Return(_) = result {
            return Ok(result);
        }
    }
    Ok(result)
}

fn eval_statement(statement: &Statement) -> Result<EvaluationResult, EvaluationError> {
    match statement {
        Statement::Expression(expression_statement) => {
            eval_expression(expression_statement.expression.as_ref())
        }
        Statement::Return(return_statement) => {
            Ok(eval_expression(return_statement.return_value.as_ref())?
                .unwrap_object()
                .into_return())
        }
        _ => Ok(Object::Null.into_value()),
    }
}

fn eval_expression(expression: &Expression) -> Result<EvaluationResult, EvaluationError> {
    match expression {
        Expression::IntegerLiteral(integer_literal_expression) => {
            Ok(Object::Integer(integer_literal_expression.value).into_value())
        }
        Expression::Boolean(boolean_expression) => {
            Ok(Object::Boolean(boolean_expression.value).into_value())
        }
        Expression::Prefix(prefix_expression) => {
            let right = eval_expression(&prefix_expression.right)?.unwrap_object();
            Ok(eval_prefix_expression(&prefix_expression.token.literal, &right)?.into_value())
        }
        Expression::Infix(infix_expression) => {
            let left = eval_expression(&infix_expression.left)?.unwrap_object();
            let right = eval_expression(&infix_expression.right)?.unwrap_object();
            Ok(eval_infix_expression(&infix_expression.token.literal, &left, &right)?.into_value())
        }
        Expression::If(if_expression) => eval_if_expression(&if_expression),

        _ => Ok(Object::Null.into_value()),
    }
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
        other => Err(EvaluationError::UnkownOperator {
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
        other => Err(EvaluationError::UnkownOperator {
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
        other => Err(EvaluationError::UnkownOperator {
            operator: other.to_string(),
            left: Some(Object::Boolean(l)),
            right: Object::Boolean(r),
        }),
    }
}

fn eval_if_expression(if_expression: &IfExpression) -> Result<EvaluationResult, EvaluationError> {
    let condition = eval_expression(if_expression.condition.as_ref())?.unwrap_object();

    if is_truthy(&condition) {
        eval_statements(&if_expression.consequence.statements)
    } else if let Some(alternative) = &if_expression.alternative {
        eval_statements(&alternative.statements)
    } else {
        Ok(EvaluationResult::Value(Object::Null))
    }
}

// Helpers

fn is_truthy(object: &Object) -> bool {
    match object {
        Object::Boolean(boolean) => *boolean,
        Object::Null => false,
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test helpers

    fn parse_input(input: &str) -> Result<Program, ParseError> {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        parser.parse_program()
    }

    fn test_eval(input: &str) -> Result<Object, EvaluationError> {
        let program = parse_input(input).expect("Parsing failed");
        eval_program(&program)
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
    fn test_eval_integer_expression() -> Result<(), String> {
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
            let evaluated = test_eval(input).unwrap();
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
        let tests: [(&str, EvaluationError); 7] = [
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
                EvaluationError::UnkownOperator {
                    operator: "-".to_string(),
                    left: None,
                    right: Object::Boolean(true),
                },
            ),
            (
                "true + false;",
                EvaluationError::UnkownOperator {
                    operator: "+".to_string(),
                    left: Some(Object::Boolean(true)),
                    right: Object::Boolean(false),
                },
            ),
            (
                "5; true + false; 5",
                EvaluationError::UnkownOperator {
                    operator: "+".to_string(),
                    left: Some(Object::Boolean(true)),
                    right: Object::Boolean(false),
                },
            ),
            (
                "if (10 > 1) { true + false; }",
                EvaluationError::UnkownOperator {
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
                EvaluationError::UnkownOperator {
                    operator: "+".to_string(),
                    left: Some(Object::Boolean(true)),
                    right: Object::Boolean(false),
                },
            ),
        ];

        for (input, expected) in tests {
            match test_eval(input) {
                Ok(obj) => panic!("expected error but got object instead: {}", obj),
                Err(err) => assert_eq!(err, expected),
            }
        }

        Ok(())
    }
}
