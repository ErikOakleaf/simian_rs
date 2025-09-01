use crate::ast::Program;
use crate::evaluator::eval_program;
use crate::lexer::Lexer;
use crate::object::Enviroment;
use crate::parser::Parser;
use std::io;
use std::io::Write;

pub fn start() -> Result<(), String> {
    let stdin = io::stdin();
    let mut enviroment = Enviroment::new();

    loop {
        print!(">> ");
        io::stdout().flush().unwrap();
        let mut buffer = String::new();
        stdin.read_line(&mut buffer).unwrap();
        let mut lexer = Lexer::new(&buffer);
        let mut parser = Parser::new(&mut lexer);
        let program = parser.parse_program().map_err(|e| format!("{:?}", e))?;
        let evaluated = eval_program(&program, &mut enviroment).map_err(|e| format!("{:?}", e))?;

        println!("{}", evaluated);
    }
}
