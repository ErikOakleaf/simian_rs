use crate::evaluator::eval_program;
use crate::lexer::Lexer;
use crate::object::{Enviroment, Object};
use crate::parser::Parser;
use std::cell::RefCell;
use std::io;
use std::io::Write;
use std::rc::Rc;

pub fn start() -> Result<(), String> {
    let stdin = io::stdin();
    let enviroment = Rc::new(RefCell::new(Enviroment::new()));

    loop {
        print!(">> ");
        io::stdout().flush().unwrap();
        let mut buffer = String::new();
        stdin.read_line(&mut buffer).unwrap();
        let mut lexer = Lexer::new(&buffer);
        let mut parser = Parser::new(&mut lexer);

        let program = match parser.parse_program() {
            Ok(p) => p,
            Err(e) => {
                println!("Parse error: {:?}", e);
                continue; 
            }
        };

        let evaluated = match eval_program(&program, &enviroment) {
            Ok(obj) => obj,
            Err(e) => {
                println!("Evaluation error: {:?}", e);
                continue;
            }
        };

        match evaluated {
            Object::Void => {}
            _ => {
                println!("{}", evaluated);
            }
        }
    }
}
