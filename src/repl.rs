use crate::ast::Program;
use crate::lexer::Lexer;
use crate::parser::{self, ParseError, Parser};
use crate::token::{Token, TokenType};
use std::io;
use std::io::Write;

pub fn start() -> Result<(), ParseError> {
    let stdin = io::stdin();

    loop {
        print!(">> ");
        io::stdout().flush().unwrap();
        let mut buffer = String::new();
        stdin.read_line(&mut buffer).unwrap();
        let mut lexer = Lexer::new(&buffer);
        let mut parser = Parser::new(&mut lexer);
        let program = parser.parse_program()?;

        println!("{}", program);
    }
}
