use crate::token::Token;

pub enum Node<'a> {
    Statement(Statement<'a>),
    Expression(Expression<'a>),
}

pub enum Statement<'a> {
    Let(LetStatement<'a>),
    Return,
}

pub enum Expression<'a> {
    Identifier(Identifier<'a>),
}

trait AstNode {
    fn token_literal(&self) -> &str;
}

// Statements

pub struct LetStatement<'a> {
    token: Token<'a>,
    identifier: Token<'a>,
    expression: Box<Expression<'a>>,
}


impl<'a> AstNode for LetStatement<'a> {
    fn token_literal(&self) -> &str {
        self.token.literal
    }
}

// Expressions

pub struct Identifier<'a> {
    token: Token<'a>,
}

impl<'a> AstNode for Identifier<'a> {
    fn token_literal(&self) -> &str {
        self.token.literal
    }
}
