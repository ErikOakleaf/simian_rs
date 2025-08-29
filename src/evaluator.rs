use crate::ast::{Expression, Program, Statement};
use crate::lexer::Lexer;
use crate::object::Object;
use crate::parser::{ParseError, Parser};

#[derive(Debug)]
pub enum EvaluationError {
    GenericError,
}

pub fn eval_program(program: &Program) -> Result<Object, EvaluationError> {
    eval_statements(&program.statements)
}

fn eval_statements(statements: &[Statement]) -> Result<Object, EvaluationError> {
    let mut result = Object::Null;
    for statement in statements {
        result = eval_statement(&statement)?;
    }
    Ok(result)
}

fn eval_statement(statement: &Statement) -> Result<Object, EvaluationError> {
    match statement {
        Statement::Expression(expression_statement) => {
            eval_expression(&expression_statement.expression)
        }
        _ => Err(EvaluationError::GenericError),
    }
}

fn eval_expression(expression: &Expression) -> Result<Object, EvaluationError> {
    match expression {
        Expression::IntegerLiteral(integer_literal_expression) => {
            Ok(Object::Integer(integer_literal_expression.value))
        }
        Expression::Boolean(boolean_expression) => {
            Ok(Object::Boolean(boolean_expression.value))
        }
        _ => Err(EvaluationError::GenericError),
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Statement;

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
    fn test_eval_integer_expression() -> Result<(), EvaluationError> {
        let tests: [(&str, i64); 2] = [("5", 5), ("10", 10)];

        for (input, expected) in tests {
            let evaluated = test_eval(input)?;
            test_integer_object(evaluated, expected);
        }

        Ok(())
    }


    #[test]
    fn test_eval_boolean_expression() -> Result<(), EvaluationError> {
        let tests: [(&str, bool); 2] = [("true", true), ("true", true)];

        for (input, expected) in tests {
            let evaluated = test_eval(input)?;
            test_boolean_object(evaluated, expected);
        }

        Ok(())
    }
}
