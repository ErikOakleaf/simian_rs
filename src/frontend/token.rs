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
    Char,

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
pub struct Token<'a> {
    pub token_type: TokenType,
    pub literal: &'a[char],
}

impl<'a> Token<'a> {
    pub fn new(token_type: TokenType, literal: &'a[char]) -> Self {
        Token {
            token_type: token_type,
            literal: literal,
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

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let literal_string: String = self.literal.iter().collect();
        write!(f, "{}", literal_string)
    }
}
