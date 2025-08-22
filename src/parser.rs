use std::thread::current;

use crate::{
    ast::{
        AstNode, Expression, ExpressionStatement, Identifier, IntegerLiteral, LetStatement,
        Program, ReturnStatement, Statement,
    },
    lexer::Lexer,
    token::{Token, TokenType},
};

pub enum Precedence {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
}

#[derive(Debug)]
pub enum ParseError {
    UnexpectedToken(Token),
    ExpectedToken {
        expected: TokenType,
        got: Token,
    },
    InvalidInteger {
        token: Token,
        source: std::num::ParseIntError,
    },
}

pub struct Parser<'a> {
    lexer: &'a mut Lexer<'a>,
    current_token: Token,
    peek_token: Token,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: &'a mut Lexer<'a>) -> Self {
        let current_token = lexer.next_token();
        let peek_token = lexer.next_token();

        Parser {
            lexer,
            current_token,
            peek_token,
        }
    }

    pub fn next_token(&mut self) {
        self.current_token = std::mem::replace(&mut self.peek_token, self.lexer.next_token());
    }

    // Parsing functions

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut program = Program { statements: vec![] };

        while self.current_token.token_type != TokenType::EOF {
            let statement = self.parse_statement()?;
            program.statements.push(statement);

            self.next_token();
        }

        Ok(program)
    }

    // Parse statements

    fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        match self.current_token.token_type {
            TokenType::Let => self.parse_let_statement(),
            TokenType::Return => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_let_statement(&mut self) -> Result<Statement, ParseError> {
        let statement_token = self.current_token.clone();
        self.expect_peek(TokenType::Ident)?;

        let identifier_token = self.current_token.clone();
        self.expect_peek(TokenType::Assign)?;

        // TODO - we are skipping the expressions until we hit a semicolon for now
        while self.current_token.token_type != TokenType::Semicolon {
            self.next_token();
        }

        let statement = LetStatement {
            token: statement_token,
            name: Identifier {
                token: identifier_token,
            },
            value: None,
        };

        Ok(Statement::Let(statement))
    }

    fn parse_return_statement(&mut self) -> Result<Statement, ParseError> {
        let statement_token = self.current_token.clone();
        self.next_token();

        // TODO - Skipping expression until hitting semicolon
        while self.current_token.token_type != TokenType::Semicolon {
            self.next_token();
        }

        // TODO - Use identifier as expression for now just to have something
        let statement = ReturnStatement {
            token: statement_token,
            return_value: Some(Box::new(Expression::Identifier(Identifier {
                token: self.current_token.clone(),
            }))),
        };

        Ok(Statement::Return(statement))
    }

    fn parse_expression_statement(&mut self) -> Result<Statement, ParseError> {
        let expression = Some(Box::new(self.parse_expression(Precedence::Lowest)?));
        let expression_statement = ExpressionStatement {
            token: self.current_token.clone(),
            expression: expression,
        };

        if self.peek_token.token_type == TokenType::Semicolon {
            self.next_token();
        }

        let statement = Statement::Expression(expression_statement);
        Ok(statement)
    }

    // Parse expressions

    fn parse_expression(&mut self, precedence: Precedence) -> Result<Expression, ParseError> {
        let prefix = match self.current_token.token_type {
            TokenType::Ident => self.parse_identifier(),
            TokenType::Int => self.parse_integer_literal(),
            _ => return Err(ParseError::UnexpectedToken(self.current_token.clone())),
        };

        prefix
    }

    fn parse_identifier(&self) -> Result<Expression, ParseError> {
        let identifier = Identifier {
            token: self.current_token.clone(),
        };
        Ok(Expression::Identifier(identifier))
    }

    fn parse_integer_literal(&mut self) -> Result<Expression, ParseError> {
        let literal: i64 =
            self.current_token
                .literal
                .parse()
                .map_err(|e| ParseError::InvalidInteger {
                    token: self.current_token.clone(),
                    source: e,
                })?;

        let integer_literal_expression = IntegerLiteral {
            token: self.current_token.clone(),
            value: literal,
        };

        Ok(Expression::IntegerLiteral(integer_literal_expression))
    }

    // Helper functions

    fn expect_peek(&mut self, expected: TokenType) -> Result<(), ParseError> {
        if self.peek_token.token_type == expected {
            self.next_token();
            Ok(())
        } else {
            Err(ParseError::ExpectedToken {
                expected: expected,
                got: self.peek_token.clone(),
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Statement;

    use super::*;

    #[test]
    fn test_let_statements() -> Result<(), ParseError> {
        let input = "let x = 5;
                    let y = 10;
                    let foobar = 838383;";

        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);

        let program = parser.parse_program()?;

        assert_eq!(
            program.statements.len(),
            3,
            "program contains {} statements not 3",
            program.statements.len()
        );

        let tests = vec!["x", "y", "foobar"];

        for (i, expected) in tests.iter().enumerate() {
            let statement = &program.statements[i];
            test_let_statement(statement, &expected)?;
        }

        Ok(())
    }

    fn test_let_statement(statement: &Statement, name: &str) -> Result<(), ParseError> {
        match statement {
            Statement::Let(let_statement) => {
                if let_statement.name.token.literal != name {
                    Err(ParseError::UnexpectedToken(let_statement.token.clone()))
                } else {
                    Ok(())
                }
            }
            Statement::Return(return_statement) => Err(ParseError::ExpectedToken {
                expected: TokenType::Let,
                got: return_statement.token.clone(),
            }),
            Statement::Expression(expression_statement) => {
                return Err(ParseError::ExpectedToken {
                    expected: TokenType::Let,
                    got: expression_statement.token.clone(),
                });
            }
        }
    }

    #[test]
    fn test_return_statements() -> Result<(), ParseError> {
        let input = "return 5;
                    return 10;
                    return 993322;";

        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);

        let program = parser.parse_program()?;

        assert_eq!(
            program.statements.len(),
            3,
            "program contains {} statements not 3",
            program.statements.len()
        );

        for statement in &program.statements {
            match statement {
                Statement::Return(return_statement) => {
                    if return_statement.token.literal != "return" {
                        return Err(ParseError::UnexpectedToken(return_statement.token.clone()));
                    }
                }
                Statement::Let(let_statement) => {
                    return Err(ParseError::ExpectedToken {
                        expected: TokenType::Return,
                        got: let_statement.token.clone(),
                    });
                }
                Statement::Expression(expression_statement) => {
                    return Err(ParseError::ExpectedToken {
                        expected: TokenType::Return,
                        got: expression_statement.token.clone(),
                    });
                }
            }
        }

        Ok(())
    }

    #[test]
    fn test_identifier_expression() -> Result<(), ParseError> {
        let input = "foobar;";

        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        let program = parser.parse_program()?;

        assert_eq!(
            program.statements.len(),
            1,
            "program contains {} statements not 1",
            program.statements.len()
        );

        let statement = &program.statements[0];
        match statement {
            Statement::Expression(expression_statement) => {
                match expression_statement
                    .expression
                    .as_ref()
                    .expect("expected expression")
                    .as_ref()
                {
                    Expression::Identifier(identifier) => {
                        assert_eq!(
                            identifier.token.literal,
                            "foobar",
                            "ident.value not 'foobar'. got={}",
                            identifier.token.literal
                        );
                    }
                    _ => panic!("unexpected identifier"),
                }
            }
            _ => panic!("unexpected statement"),
        }

        Ok(())
    }

    #[test]
    fn test_integer_literal_expression() -> Result<(), ParseError> {
        let input = "5;";

        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        let program = parser.parse_program()?;

        assert_eq!(
            program.statements.len(),
            1,
            "program contains {} statements not 1",
            program.statements.len()
        );

        let statement = &program.statements[0];
        match statement {
            Statement::Expression(expression_statement) => {
                match expression_statement
                    .expression
                    .as_ref()
                    .expect("expected expression")
                    .as_ref()
                {
                    Expression::IntegerLiteral(integer_literal) => {
                        assert_eq!(
                            integer_literal.token.literal,
                            "5",
                            "integer_literal.token.literal not '5'. got={}",
                            integer_literal.token.literal
                        );
                        assert_eq!(
                            integer_literal.value, 5,
                            "integer_literal.value not '5'. got={}",
                            integer_literal.value
                        );
                    }
                    _ => panic!("unexpected identifier"),
                }
            }
            _ => panic!("unexpected statement"),
        }

        Ok(())
    }

    fn test_integer_literal(exp: &Expression, expected: i64) {
        match exp {
            Expression::IntegerLiteral(integer_literal) => {
                assert_eq!(
                    integer_literal.value, expected,
                    "integer_literal.value not {}. got={}",
                    expected, integer_literal.value
                );
                assert_eq!(
                    integer_literal.token.literal,
                    expected.to_string(),
                    "integer_literal.token.literal not {}. got={}",
                    expected,
                    integer_literal.token.literal
                );
            }
            _ => panic!("exp not IntegerLiteral"),
        }
    }

    #[test]
    fn test_parsing_prefix_expressions() -> Result<(), ParseError> {
        let prefix_tests = vec![("!5;", "!", 5), ("-15;", "-", 15)];

        for (input, operator, literal) in prefix_tests {
            let mut lexer = Lexer::new(input);
            let mut parser = Parser::new(&mut lexer);
            let program = parser.parse_program()?;

            assert_eq!(
                program.statements.len(),
                1,
                "program contains {} statements not 1",
                program.statements.len()
            );

            let statement = &program.statements[0];

            match statement {
                Statement::Expression(expression_statement) => {
                    match expression_statement
                        .expression
                        .as_ref()
                        .expect("expected expression")
                        .as_ref()
                    {
                        Expression::Prefix(prefix_expression) => {
                            assert_eq!(
                                prefix_expression.token.literal,
                                operator,
                                "wrong operator expected {} got {}",
                                operator,
                                prefix_expression.token.literal
                            );
                            match prefix_expression.right.as_ref() {
                                Expression::IntegerLiteral(integer_literal) => {
                                    assert_eq!(
                                        integer_literal.value, literal,
                                        "wrong integer literal expected {} goct {}",
                                        literal, integer_literal.value
                                    );
                                }
                                _ => panic!("unexpected integer literal"),
                            }
                        }
                        _ => panic!("unexpected identifier"),
                    }
                }
                _ => panic!("unexpected statement"),
            }
        }

        Ok(())
    }
}
