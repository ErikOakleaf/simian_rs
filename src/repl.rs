use crate::compiler::Compiler;
use crate::evaluator::eval_program;
use crate::lexer::Lexer;
use crate::object::{Enviroment, Object};
use crate::parser::Parser;
use crate::vm::VM;
use std::cell::RefCell;
use std::io;
use std::io::Write;
use std::rc::Rc;

pub fn start(mode: usize) -> Result<(), String> {
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

        if mode == 0 {
            // interpreter mode
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
        } else {
            // compiler / vm mode
            let mut compiler = Compiler::new();
            compiler.compile_program(&program).map_err(|e| format!("Compilation error: {:?}", e));
            let mut vm = VM::new(compiler.bytecode());
            vm.run().map_err(|e| format!("VM error: {:?}", e)); 

            let stack_top = match vm.stack_top() {
                Ok(obj) => obj,
                Err(e) => {
                    println!("Evaluation error: {:?}", e);
                    continue;
                }
            };

            match stack_top {
                Object::Void => {}
                _ => {
                    println!("{}", stack_top);
                }
            }
        }
    }
}
