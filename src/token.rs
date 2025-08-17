#[derive(Debug, PartialEq, Eq)]
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

#[derive(Debug, PartialEq, Eq)]
pub struct Token<'a> {
    pub token_type: TokenType,
    pub literal: &'a str,
}
