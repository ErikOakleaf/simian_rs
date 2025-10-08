use crate::frontend::token::{Token, TokenType};

struct LexerState {
    position: usize,
    read_position: usize,
    current_char: char,
}

impl LexerState {
    fn new() -> Self {
        LexerState {
            position: 0,
            read_position: 0,
            current_char: '0',
        }
    }
}

pub struct Lexer<'a> {
    input: &'a [char],
    state: LexerState,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a [char]) -> Self {
        let mut lexer = Lexer {
            input: input,
            state: LexerState::new(),
        };
        Lexer::read_char(lexer.input, &mut lexer.state);
        lexer
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let token = match self.state.current_char {
            '=' => {
                if self.peek_char() == '=' {
                    let literal = &self.input[self.state.position..self.state.position + 2];
                    Self::read_char(self.input, &mut self.state);
                    Token::new(TokenType::EQ, literal)
                } else {
                    Token::new(
                        TokenType::Assign,
                        &self.input[self.state.position..self.state.position + 1],
                    )
                }
            }
            '!' => {
                if self.peek_char() == '=' {
                    let literal = &self.input[self.state.position..self.state.position + 2];
                    Self::read_char(self.input, &mut self.state);
                    Token::new(TokenType::NotEQ, literal)
                } else {
                    Token::new(
                        TokenType::Bang,
                        &self.input[self.state.position..self.state.position + 1],
                    )
                }
            }
            '+' => Token::new(
                TokenType::Plus,
                &self.input[self.state.position..self.state.position + 1],
            ),
            '-' => Token::new(
                TokenType::Minus,
                &self.input[self.state.position..self.state.position + 1],
            ),
            '/' => Token::new(
                TokenType::Slash,
                &self.input[self.state.position..self.state.position + 1],
            ),
            '*' => Token::new(
                TokenType::Asterisk,
                &self.input[self.state.position..self.state.position + 1],
            ),
            '<' => Token::new(TokenType::LT, &self.input[self.state.position..self.state.position + 1]),
            '>' => Token::new(TokenType::GT, &self.input[self.state.position..self.state.position + 1]),
            ';' => Token::new(
                TokenType::Semicolon,
                &self.input[self.state.position..self.state.position + 1],
            ),
            ':' => Token::new(
                TokenType::Colon,
                &self.input[self.state.position..self.state.position + 1],
            ),
            ',' => Token::new(
                TokenType::Comma,
                &self.input[self.state.position..self.state.position + 1],
            ),
            '(' => Token::new(
                TokenType::LParen,
                &self.input[self.state.position..self.state.position + 1],
            ),
            ')' => Token::new(
                TokenType::RParen,
                &self.input[self.state.position..self.state.position + 1],
            ),
            '{' => Token::new(
                TokenType::LBrace,
                &self.input[self.state.position..self.state.position + 1],
            ),
            '}' => Token::new(
                TokenType::RBrace,
                &self.input[self.state.position..self.state.position + 1],
            ),
            '[' => Token::new(
                TokenType::LBracket,
                &self.input[self.state.position..self.state.position + 1],
            ),
            ']' => Token::new(
                TokenType::RBracket,
                &self.input[self.state.position..self.state.position + 1],
            ),
            '"' => Token::new(TokenType::String, self.read_string()),
            '\'' => {
                Self::read_char(self.input, &mut self.state);

                let token = Token::new(
                    TokenType::Char,
                    &self.input[self.state.position..self.state.position + 1],
                );

                Self::read_char(self.input, &mut self.state);

                if self.state.current_char != '\'' {
                    return Token::new(
                        TokenType::Illegal,
                        &self.input[self.state.position..self.state.position + 1],
                    );
                }

                token
            }
            '\0' => Token::new(TokenType::EOF, &[]),
            _ => {
                if Self::is_letter(self.state.current_char) {
                    let literal = self.read_identifier();
                    let token_type = Token::lookup_identifier(literal);
                    return Token::new(token_type, literal);
                } else if Self::is_digit(self.state.current_char) {
                    let (literal, is_float) = self.read_number();
                    if is_float {
                        return Token::new(TokenType::Float, literal);
                    } else {
                        return Token::new(TokenType::Int, literal);
                    }
                } else {
                    Token::new(
                        TokenType::Illegal,
                        &self.input[self.state.position..self.state.position + 1],
                    )
                }
            }
        };

        Self::read_char(self.input, &mut self.state);
        token
    }

    fn read_identifier(&mut self) -> &[char] {
        let position = self.state.position;

        while Self::is_letter(self.state.current_char) {
            Self::read_char(self.input, &mut self.state);
        }

        &self.input[position..self.state.position]
    }

    fn read_number(&mut self) -> (&[char], bool) {
        let position = self.state.position;

        let mut dot_seen = false;

        while Self::is_digit(self.state.current_char) || (self.state.current_char == '.') {
            if self.state.current_char == '.' {
                if dot_seen {
                    panic!(
                        "multiple dots in number: {:?}.xx",
                        &self.input[position..self.state.position],
                    );
                }
                dot_seen = true;
            }
            Self::read_char(self.input, &mut self.state);
        }

        (&self.input[position..self.state.position], dot_seen)
    }

    fn read_char(input: &[char], state: &mut LexerState ) {
        if state.read_position >= input.len() {
            state.current_char = '\0';
        } else {
            state.current_char = input[state.read_position];
        }
        state.position = state.read_position;
        state.read_position += 1;
    }

    fn peek_char(&self) -> char {
        if self.state.read_position >= self.input.len() {
            '\0'
        } else {
            self.input[self.state.read_position]
        }
    }

    fn is_letter(character: char) -> bool {
        character.is_alphabetic() || character == '_'
    }

    fn is_digit(character: char) -> bool {
        '0' <= character && character <= '9'
    }

    fn skip_whitespace(&mut self) {
        while self.state.current_char == ' '
            || self.state.current_char == '\t'
            || self.state.current_char == '\n'
            || self.state.current_char == '\r'
        {
            Self::read_char(self.input, &mut self.state);
        }
    }

    fn read_string(&mut self) -> &'a [char] {
        let position = self.state.position + 1;
        loop {
            Self::read_char(self.input, &mut self.state);
            if self.state.current_char == '"' || self.state.current_char == '0' {
                break;
            }
        }

        &self.input[position..self.state.position]
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
            let expected_chars: Vec<char> = expected_literal.chars().collect();

            assert_eq!(tok.literal, &expected_chars, "tests[{}] literal wrong", i);
        }
    }
}
