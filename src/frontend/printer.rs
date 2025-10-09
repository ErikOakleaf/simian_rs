use crate::frontend::ast::{BlockStatement, Expression, Program, Statement};

pub fn print_program(program: &Program, input: &[char]) -> String {
    let mut results = Vec::new();

    for statement in program.statements.iter() {
        let statement_string = print_statement(statement, input);
        results.push(statement_string);
    }

    results.join("\n")
}

pub fn print_statement(statement: &Statement, input: &[char]) -> String {
    match statement {
        Statement::Let(let_statement) => {
            let statement_string = let_statement.token.literal_string(input);
            let name_string = let_statement.name.literal_string(input);

            format!(
                "{} {} = {};",
                statement_string,
                name_string,
                print_expression(let_statement.value.as_ref(), input)
            )
        }
        Statement::Return(return_statement) => {
            let statement_string = return_statement.token.literal_string(input);

            format!(
                "{} {};",
                statement_string,
                print_expression(return_statement.return_value.as_ref(), input)
            )
        }
        Statement::Expression(expression_statement) => {
            format!(
                "{};",
                print_expression(expression_statement.expression.as_ref(), input)
            )
        }
        Statement::Assign(assign_statement) => {
            format!(
                "{} = {};",
                print_expression(assign_statement.target.as_ref(), input),
                print_expression(assign_statement.value.as_ref(), input)
            )
        }
        Statement::While(while_statement) => {
            format!(
                "while ({}) {{ {} }}",
                print_expression(while_statement.condition.as_ref(), input),
                print_block_statement(&while_statement.body, input)
            )
        }
        Statement::Continue => "continue".to_string(),
        Statement::Break => "break".to_string(),
    }
}

pub fn print_expression(expression: &Expression, input: &[char]) -> String {
    match expression {
        Expression::Identifier(token) => token.literal_string(input),
        Expression::IntegerLiteral(integer_literal_expression) => {
            integer_literal_expression.token.literal_string(input)
        }
        Expression::Prefix(prefix_expression) => {
            let prefix = prefix_expression.token.literal_string(input);
            format!(
                "{}{}",
                prefix,
                print_expression(prefix_expression.right.as_ref(), input)
            )
        }
        Expression::Infix(infix_expression) => {
            let infix = infix_expression.token.literal_string(input);
            format!(
                "{} {} {}",
                print_expression(infix_expression.left.as_ref(), input),
                infix,
                print_expression(infix_expression.right.as_ref(), input)
            )
        }
        Expression::Boolean(boolean_literal_expression) => {
            boolean_literal_expression.token.literal_string(input)
        }
        Expression::If(if_expression) => {
            let mut result = String::new();

            result.push_str(&format!(
                "if ({}) {}",
                print_expression(if_expression.condition.as_ref(), input),
                print_block_statement(&if_expression.consequence, input),
            ));

            if let Some(alternative) = if_expression.alternative {
                result.push_str(&format!("else {}", print_block_statement(&alternative, input)));
            }

            result
        }
    }
}
pub fn print_block_statement(block_statement: &BlockStatement, input: &[char]) -> String {}
