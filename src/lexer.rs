use crate::token::{Token, TokenType};

pub struct Lexer<'a> {
    input: &'a str,
    position: usize,
    read_position: usize,
    char: u8,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Lexer { input, position: 0, read_position: 0, char: '\0' }
    }

    fn read_char(&mut self) {
        if self.read_position >= self.input.len() {
            self.char = 0;
        } else {
            self.char = self.input[self.read_position]
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
