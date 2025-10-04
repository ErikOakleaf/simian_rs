use crate::frontend::{
    ast::{
        ArrayLiteralExpression, AssignStatement, BlockStatement, BooleanLiteralExpression,
        CallExpression, Expression, ExpressionStatement, FunctionLiteralExpression,
        HashLiteralExpression, IdentifierExpression, IfExpression, IndexExpression,
        InfixExpression, IntegerLiteralExpression, LetStatement, PrefixExpression, Program,
        ReturnStatement, Statement, WhileStatement,
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
    Index,
}

#[allow(dead_code)]
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
        let current_token_type = &self.current_token.token_type;
        match current_token_type {
            TokenType::Let => self.parse_let_statement(),
            TokenType::Return => self.parse_return_statement(),
            TokenType::While => self.parse_while_statement(),
            _ => self.parse_expression_assign_statement(),
        }
    }

    fn parse_let_statement(&mut self) -> Result<Statement, ParseError> {
        let statement_token = self.current_token.clone();
        self.expect_peek(TokenType::Ident)?;

        let identifier_token = self.current_token.clone();
        self.expect_peek(TokenType::Assign)?;
        self.next_token();

        let mut value = self.parse_expression(Precedence::Lowest)?;

        if let Expression::Function(ref mut function_literal_expression) = value {
            function_literal_expression.name = Some(identifier_token.literal.clone());
        }

        let statement = LetStatement {
            token: statement_token,
            name: IdentifierExpression {
                token: identifier_token,
            },
            value: Box::new(value),
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

    fn parse_expression_assign_statement(&mut self) -> Result<Statement, ParseError> {
        let expression = Box::new(self.parse_expression(Precedence::Lowest)?);

        let statement;
        if self.peek_token.token_type == TokenType::Assign {
            self.next_token();
            self.next_token();

            let value = Box::new(self.parse_expression(Precedence::Lowest)?);
            let assign_statement = AssignStatement {
                target: expression,
                value: value,
            };
            statement = Statement::Assign(assign_statement);
        } else {
            let expression_statement = ExpressionStatement {
                token: self.current_token.clone(),
                expression: expression,
            };
            statement = Statement::Expression(expression_statement);
        }

        if self.peek_token.token_type == TokenType::Semicolon {
            self.next_token();
        }

        Ok(statement)
    }

    fn parse_while_statement(&mut self) -> Result<Statement, ParseError> {
        self.expect_peek(TokenType::LParen)?;
        self.next_token();

        let condition = Box::new(self.parse_expression(Precedence::Lowest)?);

        self.expect_peek(TokenType::RParen)?;
        self.expect_peek(TokenType::LBrace)?;

        let body = self.parse_block_statement()?;

        let while_statement = WhileStatement {condition: condition, body: body};

        if self.peek_token.token_type == TokenType::Semicolon {
            self.next_token();
        }

        Ok(Statement::While(while_statement))
    }

    fn parse_block_statement(&mut self) -> Result<BlockStatement, ParseError> {
        let statement_token = self.current_token.clone();
        let mut statements: Vec<Statement> = vec![];

        self.next_token();

        while self.current_token.token_type != TokenType::RBrace
            && self.current_token.token_type != TokenType::EOF
        {
            let statement = self.parse_statement()?;
            statements.push(statement);
            self.next_token();
        }

        let block_statement = BlockStatement {
            token: statement_token,
            statements: statements,
        };
        Ok(block_statement)
    }

    // Parse expressions

    fn parse_expression(&mut self, precedence: Precedence) -> Result<Expression, ParseError> {
        let mut left_expression = match self.current_token.token_type {
            TokenType::Ident => self.parse_identifier_expression()?,
            TokenType::Int => self.parse_integer_literal_expression()?,
            TokenType::Bang | TokenType::Minus => self.parse_prefix_expression()?,
            TokenType::True | TokenType::False => self.parse_boolean_expression()?,
            TokenType::LParen => self.parse_grouped_expression()?,
            TokenType::If => self.parse_if_expression()?,
            TokenType::Function => self.parse_function_literal_expression()?,
            TokenType::String => Expression::String(self.current_token.clone()),
            TokenType::LBracket => self.parse_array_literal_expression()?,
            TokenType::LBrace => self.parse_hash_literal_expression()?,
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
                TokenType::LParen => {
                    self.next_token();
                    self.parse_call_expression(left_expression)?
                }
                TokenType::LBracket => {
                    self.next_token();
                    self.parse_index_expression(left_expression)?
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

    fn parse_boolean_expression(&mut self) -> Result<Expression, ParseError> {
        let value = match self.current_token.token_type {
            TokenType::True => true,
            TokenType::False => false,
            _ => {
                return Err(ParseError::UnexpectedToken(self.current_token.clone()));
            }
        };

        let boolean_expression = BooleanLiteralExpression {
            token: self.current_token.clone(),
            value: value,
        };
        Ok(Expression::Boolean(boolean_expression))
    }

    fn parse_grouped_expression(&mut self) -> Result<Expression, ParseError> {
        self.next_token();
        let expression = self.parse_expression(Precedence::Lowest)?;

        self.expect_peek(TokenType::RParen)?;

        Ok(expression)
    }

    fn parse_if_expression(&mut self) -> Result<Expression, ParseError> {
        let expression_token = self.current_token.clone();

        self.expect_peek(TokenType::LParen)?;
        self.next_token();

        let condition = self.parse_expression(Precedence::Lowest)?;

        self.expect_peek(TokenType::RParen)?;
        self.expect_peek(TokenType::LBrace)?;

        let consequence = self.parse_block_statement()?;

        let mut alternative = None;

        // Handle else case

        if self.peek_token.token_type == TokenType::Else {
            self.next_token();
            self.expect_peek(TokenType::LBrace)?;
            alternative = Some(self.parse_block_statement()?);
        }

        let if_expression = IfExpression {
            token: expression_token,
            condition: Box::new(condition),
            consequence: consequence,
            alternative: alternative,
        };

        Ok(Expression::If(if_expression))
    }

    fn parse_function_literal_expression(&mut self) -> Result<Expression, ParseError> {
        let expression_token = self.current_token.clone();

        self.expect_peek(TokenType::LParen)?;

        let parameters = self.parse_function_parameters()?;

        self.expect_peek(TokenType::LBrace)?;

        let body = self.parse_block_statement()?;

        let function_literal_expression = FunctionLiteralExpression {
            token: expression_token,
            parameters: parameters,
            body: body,
            name: None,
        };

        Ok(Expression::Function(function_literal_expression))
    }

    fn parse_function_parameters(&mut self) -> Result<Vec<IdentifierExpression>, ParseError> {
        let mut identifiers: Vec<IdentifierExpression> = vec![];

        if self.peek_token.token_type == TokenType::RParen {
            self.next_token();
            return Ok(identifiers);
        }

        self.next_token();
        identifiers.push(IdentifierExpression {
            token: self.current_token.clone(),
        });

        while self.peek_token.token_type == TokenType::Comma {
            self.next_token();
            self.next_token();
            identifiers.push(IdentifierExpression {
                token: self.current_token.clone(),
            });
        }

        self.expect_peek(TokenType::RParen)?;

        Ok(identifiers)
    }

    fn parse_call_expression(&mut self, function: Expression) -> Result<Expression, ParseError> {
        let arguments = self.parse_call_arguments()?;
        let call_expression = CallExpression {
            token: self.current_token.clone(),
            function: Box::new(function),
            arguments: arguments,
        };
        Ok(Expression::Call(call_expression))
    }

    fn parse_call_arguments(&mut self) -> Result<Vec<Expression>, ParseError> {
        let mut arguments: Vec<Expression> = vec![];

        if self.peek_token.token_type == TokenType::RParen {
            self.next_token();
            return Ok(arguments);
        }

        self.next_token();

        arguments.push(self.parse_expression(Precedence::Lowest)?);

        while self.peek_token.token_type == TokenType::Comma {
            self.next_token();
            self.next_token();
            arguments.push(self.parse_expression(Precedence::Lowest)?);
        }

        self.expect_peek(TokenType::RParen)?;

        Ok(arguments)
    }

    fn parse_array_literal_expression(&mut self) -> Result<Expression, ParseError> {
        let token = self.current_token.clone();
        let elements = self.parse_expression_list()?;
        let array_literal_expression = ArrayLiteralExpression {
            token: token,
            elements: elements,
        };
        Ok(Expression::Array(array_literal_expression))
    }

    fn parse_expression_list(&mut self) -> Result<Vec<Expression>, ParseError> {
        let mut elements = Vec::<Expression>::new();

        if self.peek_token.token_type == TokenType::RBracket {
            self.next_token();
            return Ok(elements);
        }

        self.next_token();
        elements.push(self.parse_expression(Precedence::Lowest)?);

        while self.peek_token.token_type == TokenType::Comma {
            self.next_token();
            self.next_token();
            elements.push(self.parse_expression(Precedence::Lowest)?);
        }

        self.expect_peek(TokenType::RBracket)?;

        Ok(elements)
    }

    fn parse_hash_literal_expression(&mut self) -> Result<Expression, ParseError> {
        let token = self.current_token.clone();
        let mut pairs: Vec<(Expression, Expression)> = vec![];

        while self.peek_token.token_type != TokenType::RBrace {
            self.next_token();

            let key = self.parse_expression(Precedence::Lowest)?;
            self.expect_peek(TokenType::Colon)?;
            self.next_token();

            let value = self.parse_expression(Precedence::Lowest)?;

            pairs.push((key, value));

            if self.peek_token.token_type != TokenType::RBrace {
                self.expect_peek(TokenType::Comma)?;
            }
        }

        self.expect_peek(TokenType::RBrace)?;

        let hash_literal_expression = HashLiteralExpression {
            token: token,
            pairs: pairs,
        };

        Ok(Expression::Hash(hash_literal_expression))
    }

    fn parse_index_expression(&mut self, left: Expression) -> Result<Expression, ParseError> {
        let token = self.current_token.clone();

        self.next_token();

        let index = self.parse_expression(Precedence::Lowest)?;

        self.expect_peek(TokenType::RBracket)?;

        let index_expression = IndexExpression {
            token: token,
            left: Box::new(left),
            index: Box::new(index),
        };
        Ok(Expression::Index(index_expression))
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
            TokenType::LParen => Precedence::Call,
            TokenType::LBracket => Precedence::Index,
            _ => Precedence::Lowest,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::frontend::ast::Statement;

    use super::*;

    enum ExpectedLiteral<'a> {
        Int(i64),
        Identifier(&'a str),
        Bool(bool),
    }

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

    fn test_literal_expression(expression: &Expression, expected: ExpectedLiteral) {
        match expected {
            ExpectedLiteral::Int(expected) => test_integer_literal(expression, expected),
            ExpectedLiteral::Identifier(name) => test_identifier(expression, name),
            ExpectedLiteral::Bool(value) => test_boolean_literal(expression, value),
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

    fn test_prefix_expression(
        expression: &Expression,
        operator: &str,
        right_value: ExpectedLiteral,
    ) {
        if let Expression::Prefix(prefix_expression) = expression {
            assert_eq!(
                prefix_expression.token.literal, operator,
                "Expected operator '{}', got '{}'",
                operator, prefix_expression.token.literal
            );
            test_literal_expression(&prefix_expression.right, right_value);
        } else {
            panic!("Expression is not prefix expression");
        }
    }

    fn test_infix_expression(
        expression: &Expression,
        left_value: ExpectedLiteral,
        operator: &str,
        right_value: ExpectedLiteral,
    ) {
        if let Expression::Infix(infix_expression) = expression {
            assert_eq!(
                infix_expression.token.literal, operator,
                "Expected operator '{}', got '{}'",
                operator, infix_expression.token.literal
            );
            test_literal_expression(&infix_expression.left, left_value);
            test_literal_expression(&infix_expression.right, right_value);
        } else {
            panic!("Expression is not infix expression");
        }
    }

    fn test_boolean_literal(expression: &Expression, expected: bool) {
        match expression {
            Expression::Boolean(boolean_expression) => {
                assert_eq!(
                    boolean_expression.token.literal,
                    expected.to_string(),
                    "Boolean expression literal value is {} not {}",
                    boolean_expression.token.literal,
                    expected.to_string()
                );
                assert_eq!(
                    boolean_expression.value, expected,
                    "Boolean expression value is {} not {}",
                    boolean_expression.value, expected
                )
            }
            _ => panic!("Expression is not boolean expression"),
        }
    }

    // Tests

    #[test]
    fn test_let_statements() -> Result<(), ParseError> {
        let tests: [(&str, &str, ExpectedLiteral); 3] = [
            ("let x = 5;", "x", ExpectedLiteral::Int(5)),
            ("let y = true;", "y", ExpectedLiteral::Bool(true)),
            (
                "let foobar = y;",
                "foobar",
                ExpectedLiteral::Identifier("y"),
            ),
        ];

        for (input, expected_name, expected_value) in tests {
            let program = parse_input(input)?;

            assert_eq!(
                program.statements.len(),
                1,
                "program contains {} statements not 1",
                program.statements.len()
            );

            let let_statement = &program.statements[0];

            if let Statement::Let(let_statement) = let_statement {
                assert_eq!(
                    let_statement.name.token.literal, expected_name,
                    "statement name is not {} got {}",
                    expected_name, let_statement.name.token.literal
                );

                test_literal_expression(let_statement.value.as_ref(), expected_value);
            } else {
                panic!("Statement is not let statement");
            }
        }

        Ok(())
    }

    #[test]
    fn test_return_statements() -> Result<(), ParseError> {
        let tests: [(&str, ExpectedLiteral); 3] = [
            ("return 5;", ExpectedLiteral::Int(5)),
            ("return 10;", ExpectedLiteral::Int(10)),
            ("return 993322;", ExpectedLiteral::Int(993322)),
        ];

        for (input, expected) in tests {
            let program = parse_input(input)?;
            let statement = &program.statements[0];

            if let Statement::Return(return_statement) = statement {
                assert_eq!(
                    return_statement.token.literal, "return",
                    "return statement literal is not correct got {}",
                    return_statement.token.literal
                );

                test_literal_expression(return_statement.return_value.as_ref(), expected);
            } else {
                panic!("Statement is not return statement");
            }
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
        let prefix_tests = vec![
            ("!5;", "!", ExpectedLiteral::Int(5)),
            ("-15;", "-", ExpectedLiteral::Int(15)),
            ("!true;", "!", ExpectedLiteral::Bool(true)),
            ("!false;", "!", ExpectedLiteral::Bool(false)),
        ];

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
            (
                "5 + 5;",
                ExpectedLiteral::Int(5),
                "+",
                ExpectedLiteral::Int(5),
            ),
            (
                "5 - 5;",
                ExpectedLiteral::Int(5),
                "-",
                ExpectedLiteral::Int(5),
            ),
            (
                "5 * 5;",
                ExpectedLiteral::Int(5),
                "*",
                ExpectedLiteral::Int(5),
            ),
            (
                "5 / 5;",
                ExpectedLiteral::Int(5),
                "/",
                ExpectedLiteral::Int(5),
            ),
            (
                "5 > 5;",
                ExpectedLiteral::Int(5),
                ">",
                ExpectedLiteral::Int(5),
            ),
            (
                "5 < 5;",
                ExpectedLiteral::Int(5),
                "<",
                ExpectedLiteral::Int(5),
            ),
            (
                "5 == 5;",
                ExpectedLiteral::Int(5),
                "==",
                ExpectedLiteral::Int(5),
            ),
            (
                "5 != 5;",
                ExpectedLiteral::Int(5),
                "!=",
                ExpectedLiteral::Int(5),
            ),
            (
                "true == true",
                ExpectedLiteral::Bool(true),
                "==",
                ExpectedLiteral::Bool(true),
            ),
            (
                "true != false",
                ExpectedLiteral::Bool(true),
                "!=",
                ExpectedLiteral::Bool(false),
            ),
            (
                "false == false",
                ExpectedLiteral::Bool(false),
                "==",
                ExpectedLiteral::Bool(false),
            ),
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
            ("true", "true"),
            ("false", "false"),
            ("3 > 5 == false", "((3 > 5) == false)"),
            ("3 < 5 == true", "((3 < 5) == true)"),
            ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
            ("(5 + 5) * 2", "((5 + 5) * 2)"),
            ("2 / (5 + 5)", "(2 / (5 + 5))"),
            ("-(5 + 5)", "(-(5 + 5))"),
            ("!(true == true)", "(!(true == true))"),
            ("a + add(b * c) + d", "((a + add((b * c))) + d)"),
            (
                "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
                "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))",
            ),
            (
                "add(a + b + c * d / f + g)",
                "add((((a + b) + ((c * d) / f)) + g))",
            ),
            (
                "a * [1, 2, 3, 4][b * c] * d",
                "((a * ([1, 2, 3, 4][(b * c)])) * d)",
            ),
            (
                "add(a * b[2], b[1], 2 * [1, 2][1])",
                "add((a * (b[2])), (b[1]), (2 * ([1, 2][1])))",
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

    #[test]
    fn test_boolean_expressions() -> Result<(), ParseError> {
        let tests = [("false;", false), ("true;", true)];

        for (input, expected) in tests {
            let program = parse_input(input)?;
            let expression = get_statement_expression(&program.statements[0]);

            test_boolean_literal(expression, expected);
        }

        Ok(())
    }

    #[test]
    fn test_if_expressions() -> Result<(), ParseError> {
        let input = "if (x < y) { x }";

        let program = parse_input(input)?;

        assert_eq!(
            program.statements.len(),
            1,
            "program contains {} statements not 1",
            program.statements.len()
        );

        let expression = get_statement_expression(&program.statements[0]);

        match expression {
            Expression::If(if_expression) => {
                test_infix_expression(
                    if_expression.condition.as_ref(),
                    ExpectedLiteral::Identifier("x"),
                    "<",
                    ExpectedLiteral::Identifier("y"),
                );

                assert_eq!(
                    if_expression.consequence.statements.len(),
                    1,
                    "consequence is not 1 statements got {}",
                    if_expression.consequence.statements.len()
                );

                let consequence_expression =
                    get_statement_expression(&if_expression.consequence.statements[0]);
                test_identifier(consequence_expression, "x");

                if let Some(_alternative) = &if_expression.alternative {
                    panic!("If statement alternative exists");
                }
            }
            _ => panic!("Expression is not if expression"),
        }

        Ok(())
    }

    #[test]
    fn test_if_else_expressions() -> Result<(), ParseError> {
        let input = "if (x < y) { x } else { y }";

        let program = parse_input(input)?;

        assert_eq!(
            program.statements.len(),
            1,
            "program contains {} statements not 1",
            program.statements.len()
        );

        let expression = get_statement_expression(&program.statements[0]);

        match expression {
            Expression::If(if_expression) => {
                test_infix_expression(
                    if_expression.condition.as_ref(),
                    ExpectedLiteral::Identifier("x"),
                    "<",
                    ExpectedLiteral::Identifier("y"),
                );

                assert_eq!(
                    if_expression.consequence.statements.len(),
                    1,
                    "consequence is not 1 statements got {}",
                    if_expression.consequence.statements.len()
                );

                let consequence_expression =
                    get_statement_expression(&if_expression.consequence.statements[0]);
                test_identifier(consequence_expression, "x");

                if let Some(alternative) = &if_expression.alternative {
                    let alternative_expression =
                        get_statement_expression(&alternative.statements[0]);
                    test_identifier(alternative_expression, "y");
                } else {
                    panic!("If statement alternative does not exist");
                }
            }
            _ => panic!("Expression is not if expression"),
        }

        Ok(())
    }

    #[test]
    fn test_function_literal_parsing() -> Result<(), ParseError> {
        let input = "fn(x, y) { x + y; }";

        let program = parse_input(input)?;

        assert_eq!(
            program.statements.len(),
            1,
            "program contains {} statements not 1",
            program.statements.len()
        );

        let expression = get_statement_expression(&program.statements[0]);

        match expression {
            Expression::Function(function_expression) => {
                test_literal_expression(
                    &Expression::Identifier(function_expression.parameters[0].clone()),
                    ExpectedLiteral::Identifier("x"),
                );
                test_literal_expression(
                    &Expression::Identifier(function_expression.parameters[1].clone()),
                    ExpectedLiteral::Identifier("y"),
                );

                assert_eq!(
                    function_expression.body.statements.len(),
                    1,
                    "function_expression.body.statements does not have 1 statements. got {}",
                    function_expression.body.statements.len()
                );

                let body_statement_expression =
                    get_statement_expression(&function_expression.body.statements[0]);
                test_infix_expression(
                    body_statement_expression,
                    ExpectedLiteral::Identifier("x"),
                    "+",
                    ExpectedLiteral::Identifier("y"),
                );
            }
            _ => panic!("Expression is not function literal expression"),
        }

        Ok(())
    }

    #[test]
    fn test_function_parameter_parsing() -> Result<(), ParseError> {
        let tests: [(&str, &[&str]); 3] = [
            ("fn() {};", &[]),
            ("fn(x) {};", &["x"]),
            ("fn(x, y, z) {};", &["x", "y", "z"]),
        ];

        for (input, expected) in tests {
            let program = parse_input(input)?;

            let expression = get_statement_expression(&program.statements[0]);
            match expression {
                Expression::Function(function_expression) => {
                    assert_eq!(
                        function_expression.parameters.len(),
                        expected.len(),
                        "parameters length wrong got {} expected {}",
                        function_expression.parameters.len(),
                        expected.len()
                    );

                    for (i, identifier) in expected.iter().enumerate() {
                        test_literal_expression(
                            &Expression::Identifier(function_expression.parameters[i].clone()),
                            ExpectedLiteral::Identifier(identifier),
                        );
                    }
                }
                _ => panic!("Expression is not function expression"),
            }
        }

        Ok(())
    }

    #[test]
    fn test_call_expression_parsing() -> Result<(), ParseError> {
        let input = "add(1, 2 * 3, 4 + 5);";

        let program = parse_input(input)?;

        assert_eq!(
            program.statements.len(),
            1,
            "program does not contain 1 statement contains {} statements",
            program.statements.len()
        );

        let expression = get_statement_expression(&program.statements[0]);
        match expression {
            Expression::Call(call_expression) => {
                test_identifier(call_expression.function.as_ref(), "add");
                assert_eq!(
                    call_expression.arguments.len(),
                    3,
                    "Wrong length of arguments got {}",
                    call_expression.arguments.len()
                );

                test_literal_expression(&call_expression.arguments[0], ExpectedLiteral::Int(1));
                test_infix_expression(
                    &call_expression.arguments[1],
                    ExpectedLiteral::Int(2),
                    "*",
                    ExpectedLiteral::Int(3),
                );
                test_infix_expression(
                    &call_expression.arguments[2],
                    ExpectedLiteral::Int(4),
                    "+",
                    ExpectedLiteral::Int(5),
                );
            }
            _ => panic!("Expression is not call_expression expression"),
        }

        Ok(())
    }

    #[test]
    fn test_call_arguments_parsing() -> Result<(), ParseError> {
        let tests: [(&str, &[&str]); 3] = [
            ("add();", &[]),
            ("add(x);", &["x"]),
            ("add(x, y, z);", &["x", "y", "z"]),
        ];

        for (input, expected) in tests {
            let program = parse_input(input)?;

            let expression = get_statement_expression(&program.statements[0]);
            match expression {
                Expression::Call(call_expression) => {
                    assert_eq!(
                        call_expression.arguments.len(),
                        expected.len(),
                        "parameters length wrong got {} expected {}",
                        call_expression.arguments.len(),
                        expected.len()
                    );

                    for (i, identifier) in expected.iter().enumerate() {
                        test_literal_expression(
                            &call_expression.arguments[i],
                            ExpectedLiteral::Identifier(identifier),
                        );
                    }
                }
                _ => panic!("Expression is not function expression"),
            }
        }
        Ok(())
    }

    #[test]
    fn test_string_literal_expression() -> Result<(), ParseError> {
        let input = "\"hello world\"";

        let program = parse_input(input)?;

        let expression = get_statement_expression(&program.statements[0]);
        match expression {
            Expression::String(string_expression) => {
                assert_eq!(
                    string_expression.literal, "hello world",
                    "expected \"hello world\" got \"{}\"",
                    string_expression.literal
                )
            }
            _ => panic!("Expression is not string expression"),
        }
        Ok(())
    }

    #[test]
    fn test_parsing_array_literals() -> Result<(), ParseError> {
        let input = "[1, 2 * 2, 3 + 3]";

        let program = parse_input(input)?;

        let expression = get_statement_expression(&program.statements[0]);
        match expression {
            Expression::Array(array_literal_expression) => {
                let elements = &array_literal_expression.elements;
                test_integer_literal(&elements[0], 1);
                test_infix_expression(
                    &elements[1],
                    ExpectedLiteral::Int(2),
                    "*",
                    ExpectedLiteral::Int(2),
                );
                test_infix_expression(
                    &elements[2],
                    ExpectedLiteral::Int(3),
                    "+",
                    ExpectedLiteral::Int(3),
                );
            }
            _ => panic!("Expression is not string expression"),
        }
        Ok(())
    }

    #[test]
    fn test_parsing_hash_literal_expressions() -> Result<(), ParseError> {
        let input = "{\"one\": 1, \"two\": 2, \"three\": 3}";
        let expected = vec![("one", 1), ("two", 2), ("three", 3)];

        let program = parse_input(input)?;

        let expression = get_statement_expression(&program.statements[0]);
        match expression {
            Expression::Hash(hash_expression) => {
                assert_eq!(
                    hash_expression.pairs.len(),
                    3,
                    "pairs length is not 3 got {}",
                    hash_expression.pairs.len()
                );
                for (i, (k, v)) in expected.into_iter().enumerate() {
                    let pair = hash_expression.pairs[i].clone();
                    if let Expression::String(string_token) = pair.0 {
                        assert_eq!(
                            string_token.literal, k,
                            "key is not {} got {}",
                            k, string_token.literal
                        );
                    } else {
                        panic!("key is not string got {}", pair.0)
                    }

                    if let Expression::IntegerLiteral(integer_literal_expression) = pair.1 {
                        assert_eq!(
                            integer_literal_expression.value, v,
                            "value is not {} got {}",
                            v, integer_literal_expression.value
                        );
                    } else {
                        panic!("key is not string got {}", pair.1)
                    }
                }
            }
            _ => panic!("Expression is not hash expression"),
        }
        Ok(())
    }

    #[test]
    fn test_parsing_hash_literal_expressions_with_expressions() -> Result<(), ParseError> {
        let input = "{\"one\": 0 + 1, \"two\": 10 - 8, \"three\": 15 / 5}";
        let expected = vec![
            (ExpectedLiteral::Int(0), "+", ExpectedLiteral::Int(1)),
            (ExpectedLiteral::Int(10), "-", ExpectedLiteral::Int(8)),
            (ExpectedLiteral::Int(15), "/", ExpectedLiteral::Int(5)),
        ];

        let program = parse_input(input)?;

        let expression = get_statement_expression(&program.statements[0]);
        match expression {
            Expression::Hash(hash_expression) => {
                assert_eq!(
                    hash_expression.pairs.len(),
                    3,
                    "pairs length is not 3 got {}",
                    hash_expression.pairs.len()
                );
                for (i, (l, o, r)) in expected.into_iter().enumerate() {
                    let pair = hash_expression.pairs[i].clone();
                    test_infix_expression(&pair.1, l, o, r);
                }
            }
            _ => panic!("Expression is not hash expression"),
        }
        Ok(())
    }

    #[test]
    fn test_parsing_hash_literal_expression_empty() -> Result<(), ParseError> {
        let input = "{}";

        let program = parse_input(input)?;

        let expression = get_statement_expression(&program.statements[0]);
        match expression {
            Expression::Hash(hash_expression) => {
                assert_eq!(
                    hash_expression.pairs.len(),
                    0,
                    "pairs length is not 0 got {}",
                    hash_expression.pairs.len()
                );
            }
            _ => panic!("Expression is not hash expression"),
        }
        Ok(())
    }

    #[test]
    fn test_parsing_index_expression() -> Result<(), ParseError> {
        let input = "myArray[1 + 1]";

        let program = parse_input(input)?;

        let expression = get_statement_expression(&program.statements[0]);
        match expression {
            Expression::Index(index_expression) => {
                test_identifier(&index_expression.left, "myArray");
                test_infix_expression(
                    &index_expression.index,
                    ExpectedLiteral::Int(1),
                    "+",
                    ExpectedLiteral::Int(1),
                );
            }
            _ => panic!("Expression is not string expression"),
        }
        Ok(())
    }

    #[test]
    fn test_funciton_literal_with_name() -> Result<(), ParseError> {
        let input = "let myFunction = fn() { };";

        let program = parse_input(input)?;

        assert_eq!(program.statements.len(), 1);

        let statement = &program.statements[0];

        match statement {
            Statement::Let(let_statement) => match let_statement.value.as_ref() {
                Expression::Function(function_literal_expression) => {
                    assert_eq!(
                        "myFunction",
                        function_literal_expression.name.as_ref().unwrap(),
                        "function literal name wrong expected {} got {}",
                        "myFunction",
                        function_literal_expression.name.as_ref().unwrap()
                    );
                }
                _ => panic!("Expression is not function expression"),
            },
            other => panic!("statement {} is not let statement", other),
        }

        Ok(())
    }

    #[test]
    fn test_parsing_assign_statement() -> Result<(), ParseError> {
        let input = "a = 5";

        let program = parse_input(input)?;

        let statement = &program.statements[0];
        match statement {
            Statement::Assign(assign_statement) => {
                let expected_name = Box::new(Expression::Identifier(IdentifierExpression {
                    token: Token {
                        token_type: TokenType::Ident,
                        literal: "a".to_string(),
                    },
                }));
                let expected_value =
                    Box::new(Expression::IntegerLiteral(IntegerLiteralExpression {
                        token: Token {
                            token_type: TokenType::Int,
                            literal: "5".to_string(),
                        },
                        value: 5,
                    }));
                assert_eq!(
                    expected_name, assign_statement.target,
                    "expected name {} got {}",
                    expected_name, assign_statement.target
                );
                assert_eq!(
                    expected_value, assign_statement.value,
                    "expected value {} got {}",
                    expected_value, assign_statement.value
                );
            }
            _ => panic!("Statement is not assign statement"),
        }
        Ok(())
    }

    #[test]
    fn test_parsing_assign_statement_indexable() -> Result<(), ParseError> {
        let input = "a[0] = 5";

        let program = parse_input(input)?;

        let statement = &program.statements[0];
        match statement {
            Statement::Assign(assign_statement) => {
                let expected_target = Box::new(Expression::Index(IndexExpression {
                    token: Token {
                        token_type: TokenType::LBracket,
                        literal: "[".to_string(),
                    },
                    left: Box::new(Expression::Identifier(IdentifierExpression {
                        token: Token {
                            token_type: TokenType::Ident,
                            literal: "a".to_string(),
                        },
                    })),
                    index: Box::new(Expression::IntegerLiteral(IntegerLiteralExpression {
                        token: Token {
                            token_type: TokenType::Int,
                            literal: "0".to_string(),
                        },
                        value: 0,
                    })),
                }));
                let expected_value =
                    Box::new(Expression::IntegerLiteral(IntegerLiteralExpression {
                        token: Token {
                            token_type: TokenType::Int,
                            literal: "5".to_string(),
                        },
                        value: 5,
                    }));
                assert_eq!(
                    expected_target, assign_statement.target,
                    "expected name:\n{}\ngot:\n{}",
                    expected_target, assign_statement.target
                );
                assert_eq!(
                    expected_value, assign_statement.value,
                    "expected value:\n{}\ngot:\n{}",
                    expected_value, assign_statement.value
                );
            }
            _ => panic!("Statement is not assign statement"),
        }
        Ok(())
    }

    #[test]
    fn test_parsing_while_statements() -> Result<(), ParseError> {
        let input = "while (1 < 2) { 5 + 5 }";

        let program = parse_input(input)?;

        let statement = &program.statements[0];
        match statement {
            Statement::While(while_statement) => {
                test_infix_expression(while_statement.condition.as_ref(), ExpectedLiteral::Int(1), "<", ExpectedLiteral::Int(2));
                let body_statement = while_statement.body.statements[0].clone();
                let body_expression = match body_statement {
                    Statement::Expression(expression_statement) => expression_statement.expression,
                    _ => panic!("Statement is not expression statement"),
                };
                test_infix_expression(
                    &body_expression,
                    ExpectedLiteral::Int(5),
                    "+",
                    ExpectedLiteral::Int(5),
                );
            }
            _ => panic!("Statement is not while statement"),
        }
        Ok(())
    }
}
