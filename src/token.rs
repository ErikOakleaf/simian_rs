#[derive(Debug, PartialEq, Eq)]
pub enum TokenType {
    Illegal,
    EOF,
    Ident,
    Int,
    Comma,
    Semicolon,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Function,
    Let,
    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,
    LT,
    GT,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Token<'a> {
    pub token_type: TokenType,
    pub literal: &'a str,
}

impl<'a> Token<'a> {
    pub fn new(token_type: TokenType, literal: &'a str) -> Self {
        Token {token_type: token_type, literal: literal } 
    } 

    pub fn lookup_identifier(ident: &str) -> TokenType {
        match ident {
            "fn" => {TokenType::Function}
            "let" => {TokenType::Let}
            _ => {TokenType::Ident} 
        }
    }
}
