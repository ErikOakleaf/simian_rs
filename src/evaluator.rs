use crate::ast::{Expression, PrefixExpression, Program, Statement};
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
        _ => Object::Null 
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


        _ =>  Object::Null
    }
}

fn eval_prefix_expression(operator: &str, right: &Object) -> Object {
    match operator {
        "!" => {
            eval_bang_expression(right)
        }
        _ => {
            Object::Null
        }
    }
}

fn eval_bang_expression(right: &Object) -> Object {
    match right {
        Object::Boolean(bool) => {
           Object::Boolean(!bool)
        }
        Object::Null => {
            Object::Boolean(true)
        }
        _ => Object::Boolean(false)
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
        let tests: [(&str, i64); 2] = [("5", 5), ("10", 10)];

        for (input, expected) in tests {
            let evaluated = test_eval(input);
            test_integer_object(evaluated, expected);
        }

        Ok(())
    }

    #[test]
    fn test_eval_boolean_expression() -> Result<(), EvaluationError> {
        let tests: [(&str, bool); 2] = [("true", true), ("true", true)];

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
}
