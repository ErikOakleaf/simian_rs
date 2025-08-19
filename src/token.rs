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

    //Keywords
    Let,
    Function,
    True,
    False,
    If,
    Else,
    Return,

    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,
    LT,
    GT,
    EQ,
    NotEQ,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Token {
    pub token_type: TokenType,
    pub literal: String,
}

impl Token {
    pub fn new(token_type: TokenType, literal: &str) -> Self {
        Token {token_type: token_type, literal: literal.to_string() } 
    } 

    pub fn lookup_identifier(ident: &str) -> TokenType {
        match ident {
            "let" => {TokenType::Let}
            "fn" => {TokenType::Function}
            "true" => {TokenType::True}
            "false" => {TokenType::False}
            "if" => {TokenType::If}
            "else" => {TokenType::Else}
            "return" => {TokenType::Return}
            _ => {TokenType::Ident} 
        }
    }
}
