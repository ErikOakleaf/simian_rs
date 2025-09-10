use std::mem::MaybeUninit;

use crate::compiler::{Bytecode, Compiler};
use crate::object::Object;

const STACK_SIZE: usize = 2048;

#[derive(Debug)]
pub enum VMError {
    ReadEmptyStack,
}

pub struct Vm {
    pub instructions: Box<[u8]>,
    pub constants: Box<[Object]>,

    pub stack: [Object; STACK_SIZE],
    pub sp: usize,
}

#[allow(invalid_value)]
impl Vm {
    pub fn new(bytecode: Bytecode) -> Self {
        let constants = bytecode.constants;
        let instructions = bytecode.instructions;
        let stack: [Object; STACK_SIZE] = unsafe { MaybeUninit::uninit().assume_init() };
        let sp = 0;
        Vm {
            constants: constants,
            instructions: instructions,
            stack: stack,
            sp: sp,
        }
    }

    pub fn stack_top(&self) -> Result<&Object, VMError> {
        if self.sp == 0 {
            Err(VMError::ReadEmptyStack)
        } else {
            Ok(&self.stack[self.sp - 1])
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{ast::Program, lexer::Lexer, parser::Parser};

    #[derive(Debug)]
    struct VmTestCase {
        input: &'static str,
        expected: Object,
    }

    fn parse_input(input: &str) -> Program {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        parser.parse_program().unwrap()
    }

    fn test_integer_object(object: Object, expected: i64) {
        if let Object::Integer(integer_object) = object {
            assert_eq!(
                integer_object, expected,
                "value {} is not expected: {}",
                integer_object, expected
            )
        } else {
            panic!("object is not integer object")
        }
    }

    fn run_vm_tests(tests: &[VmTestCase]) {
        for test in tests {
            let program = parse_input(test.input);
            let mut compiler = Compiler::new();
            compiler.compile_program(&program).expect("compilation error");
            let vm = Vm::new(compiler.bytecode());
            vm.run();

            let stack_element = vm.stack_top().unwrap();
            assert_eq!(test.expected, stack_element.clone(), "expected object {} got {}", test.expected, stack_element.clone());
        }
    }
}
