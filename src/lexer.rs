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
        self.skip_whitespace();

        let token = match self.char {
            b'=' => Token::new(
                TokenType::Assign,
                &self.input[self.position..self.position + 1],
            ),
            b';' => Token::new(
                TokenType::Semicolon,
                &self.input[self.position..self.position + 1],
            ),
            b',' => Token::new(
                TokenType::Comma,
                &self.input[self.position..self.position + 1],
            ),
            b'+' => Token::new(
                TokenType::Plus,
                &self.input[self.position..self.position + 1],
            ),
            b'(' => Token::new(
                TokenType::LParen,
                &self.input[self.position..self.position + 1],
            ),
            b')' => Token::new(
                TokenType::RParen,
                &self.input[self.position..self.position + 1],
            ),
            b'{' => Token::new(
                TokenType::LBrace,
                &self.input[self.position..self.position + 1],
            ),
            b'}' => Token::new(
                TokenType::RBrace,
                &self.input[self.position..self.position + 1],
            ),
            0 => Token::new(TokenType::EOF, ""),
            _ => {
                if Self::is_letter(self.char) {
                    let literal = self.read_identifier();
                    let token_type = Token::lookup_identifier(literal);
                    return Token::new(token_type, literal);
                } else if Self::is_digit(self.char) {
                    let literal = self.read_number();
                    return Token::new(TokenType::Int, literal);
                } else {
                    Token::new(
                        TokenType::Illegal,
                        &self.input[self.position..self.position + 1],
                    )
                }
            }
        };

        self.read_char();
        token
    }

    fn read_identifier(&mut self) -> &str {
        let position = self.position;

        while Self::is_letter(self.char) {
            self.read_char();
        }

        &self.input[position..self.position]
    }

    fn read_number(&mut self) -> &str {
        let position = self.position;

        while Self::is_digit(self.char) {
            self.read_char();
        }

        &self.input[position..self.position]
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

    fn is_letter(char: u8) -> bool {
        (char >= b'a' && char <= b'z') || (char >= b'A' && char <= b'Z') || char == b'_'
    }

    fn is_digit(char: u8) -> bool {
        b'0' <= char && char <= b'9'
    }

    fn skip_whitespace(&mut self) {
        while self.char == b' ' || self.char == b'\t' || self.char == b'\n' || self.char == b'\r' {
            self.read_char();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_next_token_basic() {
        let input = "=+(){},;";
        let mut lexer = Lexer::new(input);

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
            let tok = lexer.next_token();
            assert_eq!(
                tok.token_type, *expected_type,
                "tests[{}] token type wrong",
                i
            );
            assert_eq!(tok.literal, *expected_literal, "tests[{}] literal wrong", i);
        }
    }

    #[test]
    fn test_next_token_source() {
        let input = "let five = 5;
                    let ten = 10;
                    let add = fn(x, y) {
                    x + y;
                    };
                    let result = add(five, ten);";
        let mut lexer = Lexer::new(input);
        let tests = vec![
            (TokenType::Let, "let"),
            (TokenType::Ident, "five"),
            (TokenType::Assign, "="),
            (TokenType::Int, "5"),
            (TokenType::Semicolon, ";"),
            (TokenType::Let, "let"),
            (TokenType::Ident, "ten"),
            (TokenType::Assign, "="),
            (TokenType::Int, "10"),
            (TokenType::Semicolon, ";"),
            (TokenType::Let, "let"),
            (TokenType::Ident, "add"),
            (TokenType::Assign, "="),
            (TokenType::Function, "fn"),
            (TokenType::LParen, "("),
            (TokenType::Ident, "x"),
            (TokenType::Comma, ","),
            (TokenType::Ident, "y"),
            (TokenType::RParen, ")"),
            (TokenType::LBrace, "{"),
            (TokenType::Ident, "x"),
            (TokenType::Plus, "+"),
            (TokenType::Ident, "y"),
            (TokenType::Semicolon, ";"),
            (TokenType::RBrace, "}"),
            (TokenType::Semicolon, ";"),
            (TokenType::Let, "let"),
            (TokenType::Ident, "result"),
            (TokenType::Assign, "="),
            (TokenType::Ident, "add"),
            (TokenType::LParen, "("),
            (TokenType::Ident, "five"),
            (TokenType::Comma, ","),
            (TokenType::Ident, "ten"),
            (TokenType::RParen, ")"),
            (TokenType::Semicolon, ";"),
            (TokenType::EOF, ""),
        ];

        for (i, (expected_type, expected_literal)) in tests.iter().enumerate() {
            let tok = lexer.next_token();
            assert_eq!(
                tok.token_type, *expected_type,
                "tests[{}] token type wrong",
                i
            );
            assert_eq!(tok.literal, *expected_literal, "tests[{}] literal wrong", i);
        }
    }
}
