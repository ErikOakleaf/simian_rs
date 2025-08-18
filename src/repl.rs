use crate::lexer::Lexer;
use crate::token::{Token, TokenType};
use std::io;
use std::io::{Write};

pub fn start() {
    let mut buffer = String::new();
    let stdin = io::stdin();

    loop {
        print!(">> ");
        io::stdout().flush().unwrap();
        stdin.read_line(&mut buffer).unwrap();
        let mut lexer = Lexer::new(&buffer);

        loop {
            let current_token = lexer.next_token();

            println!("(Type: {:<15} Literal: {})", format!("{:?}", current_token.token_type), current_token.literal);

            if current_token.token_type == TokenType::EOF {
                break;
            }
        }
        
    }
}
