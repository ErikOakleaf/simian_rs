use crate::token::Token;

pub enum Node {
    Statement(Statement),
    Expression(Expression),
}

pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
}

pub enum Expression {
    Identifier(Identifier),
}

pub trait AstNode {
    fn token_literal(&self) -> String;
}

// Statements

pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
}

impl<'a> AstNode for LetStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

pub struct ReturnStatement {
    pub token: Token,
    pub return_value: Expression,
}

impl<'a> AstNode for ReturnStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
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

// Program

pub struct Program {
    pub statements: Vec<Statement>,
}
