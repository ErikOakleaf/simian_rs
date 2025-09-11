use std::mem::MaybeUninit;

use crate::code::Opcode;
use crate::compiler::{Bytecode, Compiler};
use crate::object::Object;

const STACK_SIZE: usize = 2048;

#[derive(Debug)]
pub enum VMError {
    EmptyStack,
    StackOverflow,
    UnknownOpcode(u8),
    TypeMismatch {
        left: Object,
        opcode: Opcode,
        right: Object,
    },
}

pub struct VM {
    instructions: Box<[u8]>,
    constants: Box<[Object]>,

    stack: [Option<Object>; STACK_SIZE],
    sp: usize,

    last_popped: Object,
}

impl VM {
    pub fn new(bytecode: Bytecode) -> Self {
        let constants = bytecode.constants;
        let instructions = bytecode.instructions;
        let stack: [Option<Object>; STACK_SIZE] = std::array::from_fn(|_| None);
        let sp = 0;
        let last_popped = Object::Null;
        VM {
            constants: constants,
            instructions: instructions,
            stack: stack,
            sp: sp,
            last_popped: last_popped,
        }
    }

    pub fn stack_top(&self) -> Result<&Object, VMError> {
        if self.sp == 0 {
            Err(VMError::EmptyStack)
        } else {
            Ok(&self.stack[self.sp - 1].as_ref().unwrap())
        }
    }

    fn push(&mut self, object: Object) -> Result<(), VMError> {
        if self.sp == STACK_SIZE {
            return Err(VMError::StackOverflow);
        }

        self.stack[self.sp] = Some(object);
        self.sp += 1;

        Ok(())
    }

    fn pop(&mut self) -> Result<Object, VMError> {
        if self.sp == 0 {
            return Err(VMError::StackOverflow);
        }

        self.sp -= 1;
        Ok(self.stack[self.sp].take().unwrap())
    }

        
    fn pop_with_last(&mut self) -> Result<Object, VMError> {
        if self.sp == 0 {
            return Err(VMError::StackOverflow);
        }

        self.sp -= 1;
        self.last_popped = self.stack[self.sp].clone().unwrap();
        Ok(self.stack[self.sp].take().unwrap())
    }

    pub fn last_popped_stack_element(&self) -> &Object {
        &self.last_popped
    }

    pub fn run(&mut self) -> Result<(), VMError> {
        let mut ip = 0;
        while ip < self.instructions.len() {
            let opcode = self.instructions[ip];
            ip += 1;

            const LOAD_CONSTANT: u8 = Opcode::LoadConstant as u8;
            const ADD: u8 = Opcode::Add as u8;
            const POP: u8 = Opcode::Pop as u8;

            match opcode {
                LOAD_CONSTANT => {
                    let constant_index = ((self.instructions[ip] as usize) << 8)
                        | (self.instructions[ip + 1] as usize);
                    ip += 2;

                    self.push(self.constants[constant_index].clone())?;
                }
                ADD => {
                    let right = self.pop()?;
                    let left = self.pop()?;

                    match (&left, &right) {
                        (Object::Integer(l), Object::Integer(r)) => {
                            self.push(Object::Integer(*l + *r))?;
                        }
                        _ => return Err(VMError::TypeMismatch { left: left, opcode: Opcode::Add, right: right}),
                    };
                }
                POP => {
                    self.pop_with_last()?;
                }

                _ => return Err(VMError::UnknownOpcode(opcode)),
            };
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

            let stack_element = vm.last_popped_stack_element();
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
                expected: Object::Integer(3),
            },
        ];

        run_vm_tests(&tests)
    }
}
