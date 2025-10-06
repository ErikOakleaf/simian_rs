use crate::frontend::token::{Token, TokenType};

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

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let token = match self.char {
            b'=' => {
                if self.peek_char() == b'=' {
                    let literal = &self.input[self.position..self.position + 2];
                    self.read_char();
                    Token::new(TokenType::EQ, literal)
                } else {
                    Token::new(
                        TokenType::Assign,
                        &self.input[self.position..self.position + 1],
                    )
                }
            }
            b'!' => {
                if self.peek_char() == b'=' {
                    let literal = &self.input[self.position..self.position + 2];
                    self.read_char();
                    Token::new(TokenType::NotEQ, literal)
                } else {
                    Token::new(
                        TokenType::Bang,
                        &self.input[self.position..self.position + 1],
                    )
                }
            }
            b'+' => Token::new(
                TokenType::Plus,
                &self.input[self.position..self.position + 1],
            ),
            b'-' => Token::new(
                TokenType::Minus,
                &self.input[self.position..self.position + 1],
            ),
            b'/' => Token::new(
                TokenType::Slash,
                &self.input[self.position..self.position + 1],
            ),
            b'*' => Token::new(
                TokenType::Asterisk,
                &self.input[self.position..self.position + 1],
            ),
            b'<' => Token::new(TokenType::LT, &self.input[self.position..self.position + 1]),
            b'>' => Token::new(TokenType::GT, &self.input[self.position..self.position + 1]),
            b';' => Token::new(
                TokenType::Semicolon,
                &self.input[self.position..self.position + 1],
            ),
            b':' => Token::new(
                TokenType::Colon,
                &self.input[self.position..self.position + 1],
            ),
            b',' => Token::new(
                TokenType::Comma,
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
            b'[' => Token::new(
                TokenType::LBracket,
                &self.input[self.position..self.position + 1],
            ),
            b']' => Token::new(
                TokenType::RBracket,
                &self.input[self.position..self.position + 1],
            ),
            b'"' => Token::new(TokenType::String, self.read_string()),
            0 => Token::new(TokenType::EOF, ""),
            _ => {
                if Self::is_letter(self.char) {
                    let literal = self.read_identifier();
                    let token_type = Token::lookup_identifier(literal);
                    return Token::new(token_type, literal);
                } else if Self::is_digit(self.char) {
                    let (literal, is_float) = self.read_number();
                    if is_float {
                        return Token::new(TokenType::Float, literal);
                    } else {
                        return Token::new(TokenType::Int, literal);
                    }
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

    fn read_number(&mut self) -> (&str, bool) {
        let position = self.position;

        let mut dot_seen = false;

        while Self::is_digit(self.char) || (self.char == b'.') {
            if self.char == b'.' {
                if dot_seen {
                    panic!(
                        "multiple dots in number: {}.xx",
                        &self.input[position..self.position],
                    );
                }
                dot_seen = true;
            }
            self.read_char();
        }

        (&self.input[position..self.position], dot_seen)
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

    fn peek_char(&self) -> u8 {
        if self.read_position >= self.input.len() {
            0
        } else {
            self.input.as_bytes()[self.read_position]
        }
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

    fn read_string(&mut self) -> &str {
        let position = self.position + 1;
        loop {
            self.read_char();
            if self.char == b'"' || self.char == b'0' {
                break;
            }
        }

        &self.input[position..self.position]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_next_token() {
        let input = "let five = 5;
                    let ten = 10;

                    let add = fn(x, y) {
                    x + y;
                    };

                    let result = add(five, ten);
                    !-/*5;
                    5 < 10 > 5;

                    if (5 < 10) {
                        return true;
                    } else {
                        return false;
                    }

                    10 == 10;
                    10 != 9;
                    \"foobar\"
                    \"foo bar\"
                    [1, 2];
                    {\"foo\": \"bar\"}
                    5.82283
                    ";

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
            (TokenType::Bang, "!"),
            (TokenType::Minus, "-"),
            (TokenType::Slash, "/"),
            (TokenType::Asterisk, "*"),
            (TokenType::Int, "5"),
            (TokenType::Semicolon, ";"),
            (TokenType::Int, "5"),
            (TokenType::LT, "<"),
            (TokenType::Int, "10"),
            (TokenType::GT, ">"),
            (TokenType::Int, "5"),
            (TokenType::Semicolon, ";"),
            (TokenType::If, "if"),
            (TokenType::LParen, "("),
            (TokenType::Int, "5"),
            (TokenType::LT, "<"),
            (TokenType::Int, "10"),
            (TokenType::RParen, ")"),
            (TokenType::LBrace, "{"),
            (TokenType::Return, "return"),
            (TokenType::True, "true"),
            (TokenType::Semicolon, ";"),
            (TokenType::RBrace, "}"),
            (TokenType::Else, "else"),
            (TokenType::LBrace, "{"),
            (TokenType::Return, "return"),
            (TokenType::False, "false"),
            (TokenType::Semicolon, ";"),
            (TokenType::RBrace, "}"),
            (TokenType::Int, "10"),
            (TokenType::EQ, "=="),
            (TokenType::Int, "10"),
            (TokenType::Semicolon, ";"),
            (TokenType::Int, "10"),
            (TokenType::NotEQ, "!="),
            (TokenType::Int, "9"),
            (TokenType::Semicolon, ";"),
            (TokenType::String, "foobar"),
            (TokenType::String, "foo bar"),
            (TokenType::LBracket, "["),
            (TokenType::Int, "1"),
            (TokenType::Comma, ","),
            (TokenType::Int, "2"),
            (TokenType::RBracket, "]"),
            (TokenType::Semicolon, ";"),
            (TokenType::LBrace, "{"),
            (TokenType::String, "foo"),
            (TokenType::Colon, ":"),
            (TokenType::String, "bar"),
            (TokenType::RBrace, "}"),
            (TokenType::Float, "5.82283"),
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
