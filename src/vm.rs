use std::mem::MaybeUninit;

use crate::code::Opcode;
use crate::compiler::{Bytecode, Compiler};
use crate::object::Object;

const STACK_SIZE: usize = 2048;

#[derive(Debug)]
pub enum VMError {
    ReadEmptyStack,
    StackOverflow,
    UnknownOpcode(u8),
}

pub struct VM {
    pub instructions: Box<[u8]>,
    pub constants: Box<[Object]>,

    pub stack: [Object; STACK_SIZE],
    pub sp: usize,
}

#[allow(invalid_value)]
impl VM {
    pub fn new(bytecode: Bytecode) -> Self {
        let constants = bytecode.constants;
        let instructions = bytecode.instructions;
        let stack: [Object; STACK_SIZE] = std::array::from_fn(|_| Object::Null);
        let sp = 0;
        VM {
            constants: constants,
            instructions: instructions,
            stack: stack,
            sp: sp,
        }
    }

    fn stack_top(&self) -> Result<&Object, VMError> {
        if self.sp == 0 {
            Err(VMError::ReadEmptyStack)
        } else {
            Ok(&self.stack[self.sp - 1])
        }
    }

    fn push(&mut self, object: Object) -> Result<(), VMError> {
        if self.sp == STACK_SIZE {
            return Err(VMError::StackOverflow);
        }

        self.stack[self.sp] = object;
        self.sp += 1;

        Ok(())
    }

    pub fn run(&mut self) -> Result<(), VMError> {
        let mut ip = 0; 
        while ip < self.instructions.len() {
            let opcode = self.instructions[ip];
            ip += 1;

            const LOAD_CONSTANT: u8 = Opcode::LoadConstant as u8;
            
            match opcode {
                LOAD_CONSTANT => {
                    let constant_index = ((self.instructions[ip] as usize) << 8) | (self.instructions[ip + 1] as usize);
                    ip += 2;

                    self.push(self.constants[constant_index].clone())?;
                }
                _ => return Err(VMError::UnknownOpcode(opcode)),

            }

        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{ast::Program, lexer::Lexer, parser::Parser};

    #[derive(Debug)]
    struct VMTestCase {
        input: &'static str,
        expected: Object,
    }

    // Test helpers

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

    fn run_vm_tests(tests: &[VMTestCase]) -> Result<(), VMError> {
        for test in tests {
            let program = parse_input(test.input);
            let mut compiler = Compiler::new();
            compiler
                .compile_program(&program)
                .expect("compilation error");
            let mut vm = VM::new(compiler.bytecode());
            vm.run()?;

            let stack_element = vm.stack_top().unwrap();
            assert_eq!(
                test.expected,
                stack_element.clone(),
                "expected object {} got {}",
                test.expected,
                stack_element.clone()
            );
        }

        Ok(())
    }

    #[test]
    fn test_integer_arithmetic() -> Result<(), VMError> {
        let tests = vec![
            VMTestCase {
                input: "1",
                expected: Object::Integer(1),
            },
            VMTestCase {
                input: "2",
                expected: Object::Integer(2),
            },
            VMTestCase {
                input: "1 + 2",
                expected: Object::Integer(2),
            }, // TODO - fix that it should evluate to 3 later
        ];

        run_vm_tests(&tests)
    }
}
