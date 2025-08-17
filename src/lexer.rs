use crate::token::{Token, TokenType};

pub struct Lexer<'a> {
    input: &'a str,
    position: usize,
    read_position: usize,
    char: u8,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        let mut lexer = Lexer {
            input: input,
            position: 0,
            read_position: 0,
            char: 0,
        };
        lexer.read_char();

        lexer
    }

    pub fn next_token(&mut self) -> Token<'_> {
        let mut token: Token = Token {
            token_type: TokenType::Illegal,
            literal: "",
        };

        match self.char {
            b'=' => {
                token.token_type = TokenType::Assign;
                token.literal = &self.input[self.position..self.position + 1];
            },
            b';' => {
                token.token_type = TokenType::Semicolon;
                token.literal = &self.input[self.position..self.position + 1];
            },
            b',' => {
                token.token_type = TokenType::Comma;
                token.literal = &self.input[self.position..self.position + 1];
            },
            b'+' => {
                token.token_type = TokenType::Plus;
                token.literal = &self.input[self.position..self.position + 1];
            },
            b'(' => {
                token.token_type = TokenType::LParen;
                token.literal = &self.input[self.position..self.position + 1];
            },
            b')' => {
                token.token_type = TokenType::RParen;
                token.literal = &self.input[self.position..self.position + 1];
            },
            b'{' => {
                token.token_type = TokenType::LBrace;
                token.literal = &self.input[self.position..self.position + 1];
            },
            b'}' => {
                token.token_type = TokenType::RBrace;
                token.literal = &self.input[self.position..self.position + 1];
            },
            0 => {
                token.token_type = TokenType::EOF;
                token.literal = "";
            },
            _ => {}
        }

        self.read_char();
        token
    }

    fn read_char(&mut self) {
        if self.read_position >= self.input.len() {
            self.char = 0;
        } else {
            self.char = self.input.as_bytes()[self.read_position]
        }
        self.position = self.read_position;
        self.read_position += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_next_token() {
        let input = "=+(){},;";
        let mut l = Lexer::new(input);

        let tests = vec![
            (TokenType::Assign, "="),
            (TokenType::Plus, "+"),
            (TokenType::LParen, "("),
            (TokenType::RParen, ")"),
            (TokenType::LBrace, "{"),
            (TokenType::RBrace, "}"),
            (TokenType::Comma, ","),
            (TokenType::Semicolon, ";"),
            (TokenType::EOF, ""),
        ];

        for (i, (expected_type, expected_literal)) in tests.iter().enumerate() {
            let tok = l.next_token();
            assert_eq!(
                tok.token_type, *expected_type,
                "tests[{}] token type wrong",
                i
            );
            assert_eq!(tok.literal, *expected_literal, "tests[{}] literal wrong", i);
        }
    }
}
