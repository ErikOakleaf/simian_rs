use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenType {
    Illegal,
    EOF,
    Ident,
    Int,
    Float,
    Comma,
    Semicolon,
    Colon,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    String,

    //Keywords
    Let,
    Function,
    True,
    False,
    If,
    Else,
    Return,
    While,
    Continue,
    Break,

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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Token {
    pub token_type: TokenType,
    pub literal: String,
}

impl Token {
    pub fn new(token_type: TokenType, literal: &str) -> Self {
        Token {
            token_type: token_type,
            literal: literal.to_string(),
        }
    }

    pub fn lookup_identifier(ident: &str) -> TokenType {
        match ident {
            "let" => TokenType::Let,
            "fn" => TokenType::Function,
            "true" => TokenType::True,
            "false" => TokenType::False,
            "if" => TokenType::If,
            "else" => TokenType::Else,
            "return" => TokenType::Return,
            "while" => TokenType::While,
            "continue" => TokenType::Continue,
            "break" => TokenType::Break,
            _ => TokenType::Ident,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.literal)
    }
}
