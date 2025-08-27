use crate::ast::Program;
use crate::lexer::Lexer;
use crate::object::Object;
use crate::parser::{ParseError, Parser};

#[derive(Debug)]
enum EvaluationError {
    GenericError,
}

pub fn eval_program(program: &Program) -> Result<Object, EvaluationError> {
    let mut result = Object::Null;

    // itterate and match all the statements here

    Ok(result)
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
}
