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
        Expression::FloatLiteral(float_literal_expression) => {
            float_literal_expression.token.literal_string(input)
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
        Expression::String(string_token) => {
            format!("\"{}\"", string_token.literal_string(input))
        }
        Expression::Char(char_token) => {
            format!("'{}'", char_token.literal_string(input))
        }
        Expression::If(if_expression) => {
            let mut result = String::new();

            result.push_str(&format!(
                "if ({}) {}",
                print_expression(if_expression.condition.as_ref(), input),
                print_block_statement(&if_expression.consequence, input),
            ));

            if let Some(alternative) = &if_expression.alternative {
                result.push_str(&format!(
                    "else {}",
                    print_block_statement(&alternative, input)
                ));
            }

            result
        }
        Expression::Function(function_literal_expression) => {
            let params: Vec<String> = function_literal_expression
                .parameters
                .iter()
                .map(|token| format!("{}", token.literal_string(input)))
                .collect();

            format!(
                "fn ({}), {}",
                params.join(", "),
                print_block_statement(&function_literal_expression.body, input)
            )
        }
        Expression::Call(call_expression) => {
            let arguments: Vec<String> = call_expression
                .arguments
                .iter()
                .map(|expression| print_expression(expression, input))
                .collect();

            format!(
                "{}({})",
                print_expression(call_expression.function.as_ref(), input),
                arguments.join(", ")
            )
        }
        Expression::Index(index_expression) => {
            format!(
                "{}[{}]",
                print_expression(index_expression.left.as_ref(), input),
                print_expression(index_expression.index.as_ref(), input)
            )
        }
        Expression::Array(array_literal_expression) => {
            let elements: Vec<String> = array_literal_expression
                .elements
                .iter()
                .map(|element| print_expression(element, input))
                .collect();

            format!("[{}]", elements.join(", "))
        }
        Expression::Hash(hash_literal_expression) => {
            let mut parts = Vec::new();
            for (k, v) in &hash_literal_expression.pairs {
                parts.push(format!(
                    "{} : {}",
                    print_expression(k, input),
                    print_expression(v, input)
                ));
            }

            format!("{{ {} }}", parts.join(", "))
        }
    }
}
pub fn print_block_statement(block_statement: &BlockStatement, input: &[char]) -> String {
    let mut result: Vec<String> = Vec::new();

    for statement in block_statement.statements.iter() {
        result.push(print_statement(statement, input)) 
    }

    result.join("\n")
}
