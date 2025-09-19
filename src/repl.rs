use crate::backend::compiler::Compiler;
use crate::runtime::evaluator::eval_program;
use crate::frontend::Lexer;
use crate::runtime::object::{Enviroment, Object};
use crate::frontend::parser::Parser;
use crate::runtime::vm::VM;
use std::cell::RefCell;
use std::io;
use std::io::Write;
use std::rc::Rc;

pub fn start(mode: usize) -> Result<(), String> {
    let stdin = io::stdin();
    let enviroment = Rc::new(RefCell::new(Enviroment::new()));
    let mut compiler = Compiler::new();
    let mut vm = VM::new(compiler.bytecode());

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
            compiler = Compiler::new_with_state(compiler.symbol_table, compiler.constants);
            match compiler.compile_program(&program) {
                Ok(()) => {}
                Err(e) => {
                    println!("Compilation error: {:?}", e);
                    continue;
                }
            };

            vm = VM::new_with_global_store(compiler.bytecode(), vm.globals);
            match vm.run() {
                Ok(()) => {}
                Err(e) => {
                    println!("VM error: {:?}", e);
                    continue;
                }
            }

            let last_popped_element = vm.last_popped_stack_element();

            match last_popped_element {
                Object::Void => {}
                _ => {
                    println!("{}", last_popped_element);
                }
            }
        }
    }
}
