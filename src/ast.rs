use crate::token::Token;

pub enum Node {
    Statement(Statement),
    Expression(Expression),
}

pub enum Statement {
    Let(LetStatement),
    Return,
}

pub enum Expression {
    Identifier(Identifier),
}

trait AstNode {
    fn token_literal(&self) -> String;
}

// Statements

pub struct LetStatement {
    token: Token,
    identifier: Token,
    expression: Box<Expression>,
}


impl<'a> AstNode for LetStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}

// Expressions

pub struct Identifier {
    token: Token,
}

impl AstNode for Identifier {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }
}
