use std::thread::current;

use crate::{
    ast::{AstNode, Expression, Identifier, LetStatement, Program, ReturnStatement, Statement},
    lexer::Lexer,
    token::{Token, TokenType},
};

#[derive(Debug)]
pub enum ParseError {
    UnexpectedToken(Token),
    ExpectedToken { expected: TokenType, got: Token },
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
            _ => Err(ParseError::UnexpectedToken(self.current_token.clone())),
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

    // Parse expressions

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
                if let_statement.name.token_literal() != name {
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
                    if return_statement.token_literal() != "return" {
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
}
