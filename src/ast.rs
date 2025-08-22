use crate::token::{Token, TokenType};
use std::fmt;

macro_rules! impl_display_for_enum {
        ($enum_name:ident, $($variant:ident),*) => {
            impl fmt::Display for $enum_name {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    match self {
                        $(
                            $enum_name::$variant(inner) => write!(f, "{}", inner),
                    )*
                    }
                }
            }
        };
}

impl_display_for_enum!(Statement, Let, Return, Expression);
impl_display_for_enum!(Expression, Identifier, IntegerLiteral, Prefix);

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

pub enum Expression {
    Identifier(Identifier),
    IntegerLiteral(IntegerLiteral),
    Prefix(Prefix),
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

impl fmt::Display for LetStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} {} = ",
            self.token.literal,
            self.name.token.literal
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

impl fmt::Display for ReturnStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.token.literal)?;

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

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token.literal)
    }
}

pub struct IntegerLiteral {
    pub token: Token,
    pub value: i64,
}

impl fmt::Display for IntegerLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token.literal)
    }
}

pub struct Prefix {
    pub token: Token,
    pub right: Box<Expression>,
}

impl fmt::Display for Prefix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.token.literal, self.right)
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
