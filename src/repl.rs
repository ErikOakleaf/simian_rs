use crate::backend::compiler::Compiler;
use crate::frontend::Lexer;
use crate::frontend::parser::Parser;
use crate::runtime::object::{Object};
use crate::runtime::vm::VM;
use std::io;
use std::io::Write;

pub fn start() -> Result<(), String> {
    let stdin = io::stdin();
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
