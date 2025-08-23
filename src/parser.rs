use std::thread::current;

use crate::{
    ast::{
        AstNode, Expression, ExpressionStatement, IdentifierExpression, InfixExpression,
        IntegerLiteralExpression, LetStatement, PrefixExpression, Program, ReturnStatement,
        Statement,
    },
    lexer::Lexer,
    token::{Token, TokenType},
};

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
pub enum Precedence {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
}

#[derive(Debug)]
pub enum ParseError {
    UnexpectedToken(Token),
    ExpectedToken {
        expected: TokenType,
        got: Token,
    },
    InvalidInteger {
        token: Token,
        source: std::num::ParseIntError,
    },
    NoPrefixParseFunction(Token),
}

pub struct Parser<'a> {
    lexer: &'a mut Lexer<'a>,
    current_token: Token,
    peek_token: Token,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: &'a mut Lexer<'a>) -> Self {
        let current_token = lexer.next_token();
        let peek_token = lexer.next_token();

        Parser {
            lexer,
            current_token,
            peek_token,
        }
    }

    pub fn next_token(&mut self) {
        self.current_token = std::mem::replace(&mut self.peek_token, self.lexer.next_token());
    }

    // Parsing functions

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut program = Program { statements: vec![] };

        while self.current_token.token_type != TokenType::EOF {
            let statement = self.parse_statement()?;
            program.statements.push(statement);

            self.next_token();
        }

        Ok(program)
    }

    // Parse statements

    fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        match self.current_token.token_type {
            TokenType::Let => self.parse_let_statement(),
            TokenType::Return => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_let_statement(&mut self) -> Result<Statement, ParseError> {
        let statement_token = self.current_token.clone();
        self.expect_peek(TokenType::Ident)?;

        let identifier_token = self.current_token.clone();
        self.expect_peek(TokenType::Assign)?;
        self.next_token();

        let statement = LetStatement {
            token: statement_token,
            name: IdentifierExpression {
                token: identifier_token,
            },
            value: Box::new(self.parse_expression(Precedence::Lowest)?),
        };

        if self.peek_token.token_type == TokenType::Semicolon {
            self.next_token();
        }

        Ok(Statement::Let(statement))
    }

    fn parse_return_statement(&mut self) -> Result<Statement, ParseError> {
        let statement_token = self.current_token.clone();
        self.next_token();

        let statement = ReturnStatement {
            token: statement_token,
            return_value: Box::new(self.parse_expression(Precedence::Lowest)?),
        };

        if self.peek_token.token_type == TokenType::Semicolon {
            self.next_token();
        }

        Ok(Statement::Return(statement))
    }

    fn parse_expression_statement(&mut self) -> Result<Statement, ParseError> {
        let expression = Box::new(self.parse_expression(Precedence::Lowest)?);
        let expression_statement = ExpressionStatement {
            token: self.current_token.clone(),
            expression: expression,
        };

        if self.peek_token.token_type == TokenType::Semicolon {
            self.next_token();
        }

        let statement = Statement::Expression(expression_statement);
        Ok(statement)
    }

    // Parse expressions

    fn parse_expression(&mut self, precedence: Precedence) -> Result<Expression, ParseError> {
        let mut left_expression = match self.current_token.token_type {
            TokenType::Ident => self.parse_identifier_expression()?,
            TokenType::Int => self.parse_integer_literal_expression()?,
            TokenType::Bang | TokenType::Minus => self.parse_prefix_expression()?,
            _ => {
                return Err(ParseError::NoPrefixParseFunction(
                    self.current_token.clone(),
                ));
            }
        };

        while self.peek_token.token_type != TokenType::Semicolon
            && precedence < self.peek_precedence()
        {
            let infix_expression = match self.peek_token.token_type {
                TokenType::Plus
                | TokenType::Minus
                | TokenType::Slash
                | TokenType::Asterisk
                | TokenType::EQ
                | TokenType::NotEQ
                | TokenType::LT
                | TokenType::GT => {
                    self.next_token();
                    self.parse_infix_expression(left_expression)?
                }
                _ => {
                    return Ok(left_expression);
                }
            };
            left_expression = infix_expression;
        }

        Ok(left_expression)
    }

    fn parse_identifier_expression(&self) -> Result<Expression, ParseError> {
        let identifier = IdentifierExpression {
            token: self.current_token.clone(),
        };
        Ok(Expression::Identifier(identifier))
    }

    fn parse_integer_literal_expression(&mut self) -> Result<Expression, ParseError> {
        let literal: i64 =
            self.current_token
                .literal
                .parse()
                .map_err(|e| ParseError::InvalidInteger {
                    token: self.current_token.clone(),
                    source: e,
                })?;

        let integer_literal_expression = IntegerLiteralExpression {
            token: self.current_token.clone(),
            value: literal,
        };

        Ok(Expression::IntegerLiteral(integer_literal_expression))
    }

    fn parse_prefix_expression(&mut self) -> Result<Expression, ParseError> {
        let prefix = self.current_token.clone();
        self.next_token();

        let prefix_expression = PrefixExpression {
            token: prefix,
            right: Box::new(self.parse_expression(Precedence::Prefix)?),
        };
        Ok(Expression::Prefix(prefix_expression))
    }

    fn parse_infix_expression(&mut self, left: Expression) -> Result<Expression, ParseError> {
        let infix = self.current_token.clone();
        let precedence = self.current_precedence();
        self.next_token();

        let right = self.parse_expression(precedence)?;
        let infix_expression = InfixExpression {
            token: infix,
            left: Box::new(left),
            right: Box::new(right),
        };

        Ok(Expression::Infix(infix_expression))
    }

    // Helper functions

    fn expect_peek(&mut self, expected: TokenType) -> Result<(), ParseError> {
        if self.peek_token.token_type == expected {
            self.next_token();
            Ok(())
        } else {
            Err(ParseError::ExpectedToken {
                expected: expected,
                got: self.peek_token.clone(),
            })
        }
    }

    fn current_precedence(&self) -> Precedence {
        Self::precedence_of(self.current_token.clone().token_type)
    }

    fn peek_precedence(&self) -> Precedence {
        Self::precedence_of(self.peek_token.clone().token_type)
    }

    fn precedence_of(token_type: TokenType) -> Precedence {
        match token_type {
            TokenType::EQ => Precedence::Equals,
            TokenType::NotEQ => Precedence::Equals,
            TokenType::LT => Precedence::LessGreater,
            TokenType::GT => Precedence::LessGreater,
            TokenType::Plus => Precedence::Sum,
            TokenType::Minus => Precedence::Sum,
            TokenType::Slash => Precedence::Product,
            TokenType::Asterisk => Precedence::Product,
            _ => Precedence::Lowest,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Statement;

    use super::*;

    // Test helper functions

    fn parse_input(input: &str) -> Result<Program, ParseError> {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        parser.parse_program()
    }

    fn get_statement_expression(statement: &Statement) -> &Expression {
        if let Statement::Expression(expression_statement) = statement {
            &expression_statement.expression
        } else {
            panic!("Statement is not expression statement")
        }
    }

    fn test_return_statement(statement: &Statement) {
        if let Statement::Return(return_statement) = statement {
            if return_statement.token.literal != "return" {
                panic!(
                    "return statement literal is not correct got: {}",
                    return_statement.token.literal
                )
            }
        } else {
            panic!("Statement is not return statement")
        }
    }

    fn test_let_statement(statement: &Statement, name: &str) {
        if let Statement::Let(let_statement) = statement {
            if let_statement.name.token.literal != name {
                panic!(
                    "statement literal is not correct got {} expected {}",
                    let_statement.name.token.literal, name
                )
            }
        } else {
            panic!("Statement is not let statement");
        }
    }

    fn test_identifier(expression: &Expression, value: &str) {
        if let Expression::Identifier(identifier) = expression {
            assert_eq!(
                identifier.token.literal, value,
                "ident.value not {}. got={}",
                value, identifier.token.literal
            );
        } else {
            panic!("expression is not Identifier")
        }
    }

    fn test_integer_literal(expression: &Expression, expected: i64) {
        if let Expression::IntegerLiteral(integer_literal) = expression {
            assert_eq!(
                integer_literal.value, expected,
                "integer_literal.value not {}. got={}",
                expected, integer_literal.value
            );
            assert_eq!(
                integer_literal.token.literal,
                expected.to_string(),
                "integer_literal.token.literal not {}. got={}",
                expected,
                integer_literal.token.literal
            );
        } else {
            panic!("exp not IntegerLiteral")
        }
    }

    fn test_prefix_expression(expression: &Expression, operator: &str, right_value: i64) {
        if let Expression::Prefix(prefix_expression) = expression {
            assert_eq!(
                prefix_expression.token.literal, operator,
                "Expected operator '{}', got '{}'",
                operator, prefix_expression.token.literal
            );
            test_integer_literal(&prefix_expression.right, right_value);
        } else {
            panic!("Expression is not prefix expression");
        }
    }

    fn test_infix_expression(
        expression: &Expression,
        left_value: i64,
        operator: &str,
        right_value: i64,
    ) {
        if let Expression::Infix(infix_expression) = expression {
            assert_eq!(
                infix_expression.token.literal, operator,
                "Expected operator '{}', got '{}'",
                operator, infix_expression.token.literal
            );
            test_integer_literal(&infix_expression.left, left_value);
            test_integer_literal(&infix_expression.right, right_value);
        } else {
            panic!("Expression is not infix expression");
        }
    }

    // Tests

    #[test]
    fn test_let_statements() -> Result<(), ParseError> {
        let input = "let x = 5;
                    let y = 10;
                    let foobar = 838383;";

        let program = parse_input(input)?;

        assert_eq!(
            program.statements.len(),
            3,
            "program contains {} statements not 3",
            program.statements.len()
        );

        let tests = vec!["x", "y", "foobar"];

        for (i, expected) in tests.iter().enumerate() {
            let statement = &program.statements[i];
            test_let_statement(statement, &expected);
        }

        Ok(())
    }

    #[test]
    fn test_return_statements() -> Result<(), ParseError> {
        let input = "return 5;
                    return 10;
                    return 993322;";

        let program = parse_input(input)?;

        assert_eq!(
            program.statements.len(),
            3,
            "program contains {} statements not 3",
            program.statements.len()
        );

        for statement in &program.statements {
            test_return_statement(statement);
        }

        Ok(())
    }

    #[test]
    fn test_identifier_expression() -> Result<(), ParseError> {
        let input = "foobar;";

        let program = parse_input(input)?;

        assert_eq!(
            program.statements.len(),
            1,
            "program contains {} statements not 1",
            program.statements.len()
        );

        let expression = get_statement_expression(&program.statements[0]);
        test_identifier(expression, "foobar");

        Ok(())
    }

    #[test]
    fn test_integer_literal_expression() -> Result<(), ParseError> {
        let input = "5;";

        let program = parse_input(input)?;

        assert_eq!(
            program.statements.len(),
            1,
            "program contains {} statements not 1",
            program.statements.len()
        );

        let expression = get_statement_expression(&program.statements[0]);
        test_integer_literal(expression, 5);

        Ok(())
    }

    #[test]
    fn test_parsing_prefix_expressions() -> Result<(), ParseError> {
        let prefix_tests = vec![("!5;", "!", 5), ("-15;", "-", 15)];

        for (input, operator, literal) in prefix_tests {
            let program = parse_input(input)?;

            assert_eq!(
                program.statements.len(),
                1,
                "program contains {} statements not 1",
                program.statements.len()
            );

            let expression = get_statement_expression(&program.statements[0]);
            test_prefix_expression(expression, operator, literal);
        }

        Ok(())
    }

    #[test]
    fn test_parsing_infix_expressions() -> Result<(), ParseError> {
        let prefix_tests = vec![
            ("5 + 5;", 5, "+", 5),
            ("5 - 5;", 5, "-", 5),
            ("5 * 5;", 5, "*", 5),
            ("5 / 5;", 5, "/", 5),
            ("5 > 5;", 5, ">", 5),
            ("5 < 5;", 5, "<", 5),
            ("5 == 5;", 5, "==", 5),
            ("5 != 5;", 5, "!=", 5),
        ];

        for (input, literal_left, operator, literal_right) in prefix_tests {
            let program = parse_input(input)?;

            assert_eq!(
                program.statements.len(),
                1,
                "program contains {} statements not 1",
                program.statements.len()
            );

            let expression = get_statement_expression(&program.statements[0]);
            test_infix_expression(expression, literal_left, operator, literal_right);
        }

        Ok(())
    }

    #[test]
    fn test_operator_precedence_parsing() -> Result<(), ParseError> {
        let tests = vec![
            ("-a * b", "((-a) * b)"),
            ("!-a", "(!(-a))"),
            ("a + b + c", "((a + b) + c)"),
            ("a + b - c", "((a + b) - c)"),
            ("a * b * c", "((a * b) * c)"),
            ("a * b / c", "((a * b) / c)"),
            ("a + b / c", "(a + (b / c))"),
            ("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)"),
            ("3 + 4; -5 * 5", "(3 + 4)((-5) * 5)"),
            ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
            ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))"),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
        ];

        for (input, actual) in tests {
            let program = parse_input(input)?;
            let program_string = format!("{}", program);

            assert_eq!(
                program_string, actual,
                "precdence is not correct expected {} got {}",
                actual, program_string
            )
        }

        Ok(())
    }
}
