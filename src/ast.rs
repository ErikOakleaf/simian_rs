use crate::token::{Token, TokenType};
use std::fmt;

// Enums

pub enum Node {
    Statement(Statement),
    Expression(Expression),
}

pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Statement::Let(statement) => write!(f, "{}", statement),
            Statement::Return(statement) => write!(f, "{}", statement),
            Statement::Expression(statement) => write!(f, "{}", statement),
        }
    }
}

pub enum Expression {
    Identifier(Identifier),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Identifier(ident) => write!(f, "{}", ident),
        }
    }
}

// Traits

pub trait AstNode {
    fn token_literal(&self) -> String;
}

// Statements

pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: Option<Box<Expression>>,
}

impl<'a> AstNode for LetStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl fmt::Display for LetStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} {} = ",
            self.token_literal(),
            self.name.token_literal()
        )?;

        if let Some(expr) = &self.value {
            write!(f, "{}", expr)?;
        }

        write!(f, ";")
    }
}

pub struct ReturnStatement {
    pub token: Token,
    pub return_value: Option<Box<Expression>>,
}

impl<'a> AstNode for ReturnStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl fmt::Display for ReturnStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.token_literal())?;

        if let Some(expr) = &self.return_value {
            write!(f, " {}", expr)?;
        }

        write!(f, ";")
    }
}

pub struct ExpressionStatement {
    pub token: Token,
    pub expression: Option<Box<Expression>>,
}

impl AstNode for ExpressionStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl fmt::Display for ExpressionStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(expr) = &self.expression {
            write!(f, "{}", expr)
        } else {
            Ok(())
        }
    }
}

// Expressions

pub struct Identifier {
    pub token: Token,
}

impl AstNode for Identifier {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token_literal())
    }
}

// Program

pub struct Program {
    pub statements: Vec<Statement>,
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for statement in &self.statements {
            write!(f, "{}", statement)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Statement;

    use super::*;

    #[test]
    pub fn test_display() {
        let program = Program {
            statements: vec![Statement::Let(LetStatement {
                token: Token {
                    token_type: TokenType::Let,
                    literal: "let".to_string(),
                },
                name: Identifier {
                    token: Token {
                        token_type: TokenType::Ident,
                        literal: "myVar".to_string(),
                    },
                },
                value: Some(Box::new(Expression::Identifier(Identifier {
                    token: Token {
                        token_type: TokenType::Ident,
                        literal: "anotherVar".to_string(),
                    },
                }))),
            })],
        };

        assert_eq!(format!("{}", program), "let myVar = anotherVar;");
    }
}
