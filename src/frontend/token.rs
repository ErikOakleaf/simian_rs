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
    pub fn new(token_type: TokenType, literal: &[char]) -> Self {
        let literal_string: String = literal.iter().collect();
        Token {
            token_type: token_type,
            literal: literal_string,
        }
    }

    pub fn lookup_identifier(ident: &[char]) -> TokenType {
        match ident.len() {
            2 => match ident {
                ['i', 'f'] => TokenType::If,
                ['f', 'n'] => TokenType::Function,
                _ => TokenType::Ident,
            },
            3 => match ident {
                ['l', 'e', 't'] => TokenType::Let,
                _ => TokenType::Ident,
            },
            4 => match ident {
                ['t', 'r', 'u', 'e'] => TokenType::True,
                ['e', 'l', 's', 'e'] => TokenType::Else,
                _ => TokenType::Ident,
            },
            5 => match ident {
                ['f', 'a', 'l', 's', 'e'] => TokenType::False,
                ['w', 'h', 'i', 'l', 'e'] => TokenType::While,
                ['b', 'r', 'e', 'a', 'k'] => TokenType::Break,
                _ => TokenType::Ident,
            },
            6 => match ident {
                ['r', 'e', 't', 'u', 'r', 'n'] => TokenType::Return,
                _ => TokenType::Ident,
            },
            8 => match ident {
                ['c', 'o', 'n', 't', 'i', 'n', 'u', 'e'] => TokenType::Continue,
                _ => TokenType::Ident,
            },
            _ => TokenType::Ident,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.literal)
    }
}
