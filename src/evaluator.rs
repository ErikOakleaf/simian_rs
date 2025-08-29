use crate::ast::{Expression, IfExpression, PrefixExpression, Program, Statement};
use crate::lexer::Lexer;
use crate::object::Object;
use crate::parser::{ParseError, Parser};

#[derive(Debug)]
pub enum EvaluationError {
    GenericError,
}

pub fn eval_program(program: &Program) -> Object {
    eval_statements(&program.statements)
}

fn eval_statements(statements: &[Statement]) -> Object {
    let mut result = Object::Null;
    for statement in statements {
        result = eval_statement(&statement);
    }
    result
}

fn eval_statement(statement: &Statement) -> Object {
    match statement {
        Statement::Expression(expression_statement) => {
            eval_expression(&expression_statement.expression)
        }
        _ => Object::Null,
    }
}

fn eval_expression(expression: &Expression) -> Object {
    match expression {
        Expression::IntegerLiteral(integer_literal_expression) => {
            Object::Integer(integer_literal_expression.value)
        }
        Expression::Boolean(boolean_expression) => Object::Boolean(boolean_expression.value),
        Expression::Prefix(prefix_expression) => {
            let right = eval_expression(&prefix_expression.right);
            eval_prefix_expression(&prefix_expression.token.literal, &right)
        }
        Expression::Infix(infix_expression) => {
            let left = eval_expression(&infix_expression.left);
            let right = eval_expression(&infix_expression.right);
            eval_infix_expression(&infix_expression.token.literal, &left, &right)
        }
        Expression::If(if_expression) => eval_if_expression(&if_expression),

        _ => Object::Null,
    }
}

fn eval_prefix_expression(operator: &str, right: &Object) -> Object {
    match operator {
        "!" => eval_bang_operator_expression(right),
        "-" => eval_minus_prefix_operator_expression(right),
        _ => Object::Null,
    }
}

fn eval_bang_operator_expression(right: &Object) -> Object {
    match right {
        Object::Boolean(boolean) => Object::Boolean(!boolean),
        Object::Null => Object::Boolean(true),
        _ => Object::Boolean(false),
    }
}

fn eval_minus_prefix_operator_expression(right: &Object) -> Object {
    if let Object::Integer(integer) = right {
        Object::Integer(-integer)
    } else {
        Object::Null
    }
}

fn eval_infix_expression(operator: &str, left: &Object, right: &Object) -> Object {
    match (left, right) {
        (Object::Integer(l), Object::Integer(r)) => eval_integer_infix_expression(operator, *l, *r),
        (Object::Boolean(l), Object::Boolean(r)) => eval_bool_infix_expression(operator, *l, *r),
        _ => Object::Null,
    }
}

fn eval_integer_infix_expression(operator: &str, l: i64, r: i64) -> Object {
    match operator {
        "+" => Object::Integer(l + r),
        "-" => Object::Integer(l - r),
        "*" => Object::Integer(l * r),
        "/" => Object::Integer(l / r),
        ">" => Object::Boolean(l > r),
        "<" => Object::Boolean(l < r),
        "==" => Object::Boolean(l == r),
        "!=" => Object::Boolean(l != r),
        _ => Object::Null,
    }
}

fn eval_bool_infix_expression(operator: &str, l: bool, r: bool) -> Object {
    match operator {
        "==" => Object::Boolean(l == r),
        "!=" => Object::Boolean(l != r),
        _ => Object::Null,
    }
}

fn eval_if_expression(if_expression: &IfExpression) -> Object {
    let condition = eval_expression(if_expression.condition.as_ref());
    if is_truthy(&condition) {
        eval_statements(&if_expression.consequence.statements)
    } else if let Some(alternative) = &if_expression.alternative {
        eval_statements(&alternative.statements)
    } else {
        Object::Null
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

    fn test_eval(input: &str) -> Object {
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
            let evaluated = test_eval(input);
            test_integer_object(evaluated, expected);
        }

        Ok(())
    }

    #[test]
    fn test_eval_boolean_expression() -> Result<(), EvaluationError> {
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
            let evaluated = test_eval(input);
            test_boolean_object(evaluated, expected);
        }

        Ok(())
    }

    #[test]
    fn test_bang_operator() -> Result<(), EvaluationError> {
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
            let evaluated = test_eval(input);
            test_boolean_object(evaluated, expected);
        }

        Ok(())
    }

    #[test]
    fn test_if_else_expression() -> Result<(), EvaluationError> {
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
            let evaluated = test_eval(input);
            if let Object::Integer(integer) = expected {
                test_integer_object(evaluated, integer);
            } else {
                assert!(matches!(evaluated, Object::Null), "Object is not Null");
            }
        }

        Ok(())
    }
}
