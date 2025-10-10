use crate::backend::SymbolTable;
use crate::backend::compiler::Compiler;
use crate::frontend::parser::Parser;
use crate::runtime::builtins::BUILTINS;
use crate::runtime::object::Object;
use crate::runtime::vm::VM;
use std::io;
use std::io::Write;

pub fn start() -> Result<(), String> {
    let stdin = io::stdin();

    let mut symbol_table = SymbolTable::new();
    for (i, builtin) in BUILTINS.iter().enumerate() {
        symbol_table
            .borrow_mut()
            .define_builtin(i as u16, builtin.name);
    }
    let mut constants = Vec::<Object>::new();

    let temp_compiler = Compiler::new(&[]);
    let mut vm = VM::new(temp_compiler.bytecode());

    loop {
        print!(">> ");
        io::stdout().flush().unwrap();
        let mut buffer = String::new();
        stdin.read_line(&mut buffer).unwrap();

        let chars: Vec<char> = buffer.chars().collect();
        let mut parser = Parser::new(&chars);

        let program = match parser.parse_program() {
            Ok(p) => p,
            Err(e) => {
                println!("Parse error: {:?}", e);
                continue;
            }
        };

        let mut compiler =
            Compiler::new_with_state(&chars, symbol_table.clone(), constants.clone());
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

        symbol_table = compiler.symbol_table;
        constants = compiler.constants;
    }
}
