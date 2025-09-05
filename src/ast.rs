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
impl_display_for_enum!(
    Expression,
    Identifier,
    IntegerLiteral,
    Prefix,
    Infix,
    Boolean,
    If,
    Function,
    Call,
    String
);

// Enums
pub enum Node {
    Statement(Statement),
    Expression(Expression),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Identifier(IdentifierExpression),
    IntegerLiteral(IntegerLiteralExpression),
    Prefix(PrefixExpression),
    Infix(InfixExpression),
    Boolean(BooleanLiteralExpression),
    If(IfExpression),
    Function(FunctionLiteralExpression),
    Call(CallExpression),
    String(Token),
}

// Statements

#[derive(Debug, Clone, PartialEq)]
pub struct LetStatement {
    pub token: Token,
    pub name: IdentifierExpression,
    pub value: Box<Expression>,
}

impl fmt::Display for LetStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} {} = {};",
            self.token.literal, self.name.token.literal, self.value
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStatement {
    pub token: Token,
    pub return_value: Box<Expression>,
}

impl fmt::Display for ReturnStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {};", self.token.literal, self.return_value)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExpressionStatement {
    pub token: Token,
    pub expression: Box<Expression>,
}

impl fmt::Display for ExpressionStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.expression)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockStatement {
    pub token: Token,
    pub statements: Vec<Statement>,
}

impl fmt::Display for BlockStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for statement in &self.statements {
            write!(f, "{}", statement)?;
        }

        Ok(())
    }
}

// Expressions

#[derive(Debug, Clone, PartialEq)]
pub struct IdentifierExpression {
    pub token: Token,
}

impl fmt::Display for IdentifierExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token.literal)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IntegerLiteralExpression {
    pub token: Token,
    pub value: i64,
}

impl fmt::Display for IntegerLiteralExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token.literal)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct PrefixExpression {
    pub token: Token,
    pub right: Box<Expression>,
}

impl fmt::Display for PrefixExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}{})", self.token.literal, self.right)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct InfixExpression {
    pub token: Token,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
}

impl fmt::Display for InfixExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {} {})", self.left, self.token.literal, self.right)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BooleanLiteralExpression {
    pub token: Token,
    pub value: bool,
}

impl fmt::Display for BooleanLiteralExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token.literal)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfExpression {
    pub token: Token,
    pub condition: Box<Expression>,
    pub consequence: BlockStatement,
    pub alternative: Option<BlockStatement>,
}

impl fmt::Display for IfExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "if{} {}", self.condition, self.consequence)?;

        if let Some(alternative) = &self.alternative {
            write!(f, "else {}", alternative)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionLiteralExpression {
    pub token: Token,
    pub parameters: Vec<IdentifierExpression>,
    pub body: BlockStatement,
}

impl fmt::Display for FunctionLiteralExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params: Vec<String> = self.parameters.iter().map(|p| format!("{}", p)).collect();

        write!(
            f,
            "{} ({}) {}",
            self.token.literal,
            params.join(", "),
            self.body
        )?;

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpression {
    pub token: Token,
    pub function: Box<Expression>,
    pub arguments: Vec<Expression>,
}

impl fmt::Display for CallExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let arguments: Vec<String> = self.arguments.iter().map(|p| format!("{}", p)).collect();

        write!(f, "{}({})", self.function, arguments.join(", "),)?;

        Ok(())
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
                name: IdentifierExpression {
                    token: Token {
                        token_type: TokenType::Ident,
                        literal: "myVar".to_string(),
                    },
                },
                value: Box::new(Expression::Identifier(IdentifierExpression {
                    token: Token {
                        token_type: TokenType::Ident,
                        literal: "anotherVar".to_string(),
                    },
                })),
            })],
        };

        assert_eq!(format!("{}", program), "let myVar = anotherVar;");
    }
}
