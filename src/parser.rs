use crate::{
    ast::{Program, LetStatement, AstNode},
    lexer::Lexer,
    token::{Token, TokenType},
};

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

    pub fn parse_program(&mut self) -> Program {
        return Program { statements: vec![] };
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

        let program = parser.parse_program();

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
