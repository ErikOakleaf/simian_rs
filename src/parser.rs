use std::thread::current;

use crate::{
    ast::{AstNode, LetStatement, Program, Statement, Identifier},
    lexer::Lexer,
    token::{Token, TokenType},
};

#[derive(Debug)]
pub enum ParseError {
    UnexpectedToken(Token),
    ExpectedToken(TokenType, Token),
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

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut program = Program { statements: vec![] };

        while self.current_token.token_type != TokenType::EOF {
            let statement = self.parse_statement()?;
            program.statements.push(statement);

            self.next_token();
        }

        Ok(program)
    }

    fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        match self.current_token.token_type {
            TokenType::Let => self.parse_let_statement(),
            _ => Err(ParseError::UnexpectedToken(self.current_token.clone()))
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
            name: Identifier {token: identifier_token},
        };

        Ok(Statement::Let(statement))
    }

    fn expect_peek(&mut self, expected: TokenType) -> Result<(), ParseError> {
        if self.peek_token.token_type == expected {
            self.next_token();
            Ok(())
        } else {
            Err(ParseError::UnexpectedToken(self.peek_token.clone()))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Statement;

    use super::*;

    #[test]
    fn test_let_statements() -> Result<(), String> {
        let input = "let x = 5;
                    let y = 10;
                    let foobar = 838383;";

        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);

        let program = parser.parse_program().unwrap();

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

    fn test_let_statement(statement: &Statement, name: &str) -> Result<(), String> {
        match statement {
           Statement::Let(let_statement)  => {
                
                if let_statement.name.token_literal() != name {
                    Err(format!("LetStatement identifier mismatch: expected '{}', got '{}'", name, let_statement.name.token_literal()))
                } else {
                    Ok(())
                }
            }
            _ => {
                 Err("Statment Is not let statement".into())
            }
        }
    }
}
