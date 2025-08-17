#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenType {
    Illegal,
    EOF,
    Ident,
    Int,
    Assign,
    Plus,
    Comma,
    Semicolon,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Function,
    Let,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    token_type: TokenType,
    literal: &'a str,
}
