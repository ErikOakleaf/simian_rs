use crate::frontend::token::{Token, TokenType};

pub struct Lexer<'a> {
    input: &'a [char],
    position: usize,
    read_position: usize,
    line: usize,
    column: usize,
    current_char: char,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a [char]) -> Self {
        let lexer = Lexer {
            input: input,
            position: 0,
            read_position: 0,
            line: 1,
            column: 0,
            current_char: '0',
        };
        lexer
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let token = match self.current_char {
            '=' => {
                if self.peek_char() == '=' {
                    self.read_char();
                    Token::new(
                        TokenType::EQ,
                        self.position,
                        self.position + 2,
                        self.line,
                        self.column,
                    )
                } else {
                    Token::new(
                        TokenType::Assign,
                        self.position,
                        self.position + 1,
                        self.line,
                        self.column,
                    )
                }
            }
            '!' => {
                if self.peek_char() == '=' {
                    let literal = &self.input[self.position..self.position + 2];
                    self.read_char();
                    Token::new(
                        TokenType::NotEQ,
                        self.position,
                        self.position + 2,
                        self.line,
                        self.column,
                    )
                } else {
                    Token::new(
                        TokenType::Bang,
                        self.position,
                        self.position + 1,
                        self.line,
                        self.column,
                    )
                }
            }
            '+' => Token::new(
                TokenType::Plus,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            '-' => Token::new(
                TokenType::Minus,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            '/' => Token::new(
                TokenType::Slash,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            '*' => Token::new(
                TokenType::Asterisk,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            '<' => Token::new(
                TokenType::LT,
                self.position,
                self.position + 1,
                self.line,
                self.column,
            ),
            '>' => Token::new(
                TokenType::GT,
                self.position,
                self.position + 1,
                self.line,
                self.column,
            ),
            ';' => Token::new(
                TokenType::Semicolon,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            ':' => Token::new(
                TokenType::Colon,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            ',' => Token::new(
                TokenType::Comma,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            '(' => Token::new(
                TokenType::LParen,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            ')' => Token::new(
                TokenType::RParen,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            '{' => Token::new(
                TokenType::LBrace,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            '}' => Token::new(
                TokenType::RBrace,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            '[' => Token::new(
                TokenType::LBracket,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            ']' => Token::new(
                TokenType::RBracket,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            '"' => {
                let column = self.column;
                let (start, end) = self.read_string();
                Token::new(TokenType::String, start, end, self.line, column)
            }
            '\'' => {
                self.read_char();

                let token = Token::new(
                    TokenType::Char,
                    self.position,
                    self.position,
                    self.line,
                    self.column,
                );

                self.read_char();

                if self.current_char != '\'' {
                    return Token::new(
                        TokenType::Illegal,
                        self.position,
                        self.position,
                        self.line,
                        self.column,
                    );
                }

                token
            }
            '\0' => Token::new(
                TokenType::EOF,
                self.position,
                self.position,
                self.line,
                self.column,
            ),
            _ => {
                if Self::is_letter(self.current_char) {
                    let column = self.column;
                    let (start, end) = self.read_identifier();

                    let token_type = Token::lookup_identifier(&self.input[start..end]);

                    return Token::new(token_type, start, end, self.line, column);

                } else if Self::is_digit(self.current_char) {
                    let column = self.column;
                    let ((start, end), is_float) = self.read_number();
                    if is_float {
                        return Token::new(TokenType::Float, start, end, self.line, column);
                    } else {
                        return Token::new(TokenType::Int, start, end, self.line, column);
                    }
                } else {
                    Token::new(
                        TokenType::Illegal,
                        self.position,
                        self.position + 1,
                        self.line,
                        self.column,
                    )
                }
            }
        };

        self.read_char();
        token
    }

    fn read_identifier(&mut self) -> (usize, usize) {
        let start_position = self.position;

        while Self::is_letter(self.current_char) {
            self.read_char();
        }

        (start_position, self.position)
    }

    fn read_number(&mut self) -> ((usize, usize), bool) {
        let start_position = self.position;

        let mut dot_seen = false;

        while Self::is_digit(self.current_char) || (self.current_char == '.') {
            if self.current_char == '.' {
                if dot_seen {
                    panic!(
                        "multiple dots in number: {:?}.xx",
                        &self.input[start_position..self.position],
                    );
                }
                dot_seen = true;
            }
            self.read_char();
        }

        ((start_position, self.position), dot_seen)
    }

    fn read_char(&mut self) {
        if self.read_position >= self.input.len() {
            self.current_char = '\0';
        } else {
            self.current_char = self.input[self.read_position];
        }

        if self.current_char == '\n' {
            self.line += 1;
            self.column = 0;
        } else {
            self.column += 1;
        }

        self.position = self.read_position;
        self.read_position += 1;
    }

    fn peek_char(&self) -> char {
        if self.read_position >= self.input.len() {
            '\0'
        } else {
            self.input[self.read_position]
        }
    }

    fn is_letter(character: char) -> bool {
        character.is_alphabetic() || character == '_'
    }

    fn is_digit(character: char) -> bool {
        '0' <= character && character <= '9'
    }

    fn skip_whitespace(&mut self) {
        while self.current_char == ' '
            || self.current_char == '\t'
            || self.current_char == '\n'
            || self.current_char == '\r'
        {
            self.read_char();
        }
    }

    fn read_string(&mut self) -> (usize, usize) {
        let start_position = self.position + 1;
        loop {
            self.read_char();
            if self.current_char == '"' || self.current_char == '0' {
                break;
            }
        }

        (start_position, self.position)
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
                    \"🐒🐵\"
                    '🐒'
                    ";

        let chars: Vec<char> = input.chars().collect();
        let mut lexer = Lexer::new(&chars);

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
            (TokenType::String, "🐒🐵"),
            (TokenType::Char, "🐒"),
            (TokenType::EOF, ""),
        ];

        for (i, (expected_type, expected_literal)) in tests.iter().enumerate() {
            let tok = lexer.next_token();
            assert_eq!(
                tok.token_type, *expected_type,
                "tests[{}] token type wrong",
                i
            );
            // let expected_chars: Vec<char> = expected_literal.chars().collect();

            let actual_string: String = lexer.input[tok.start..tok.end].iter().collect();

            assert_eq!(
                actual_string, *expected_literal,
                "tests[{}] literal wrong",
                i
            );
        }
    }
}
