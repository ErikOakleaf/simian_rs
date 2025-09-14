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
    UnknownOperator {
        operand: String,
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
            return Err(VMError::EmptyStack);
        }

        self.sp -= 1;
        Ok(self.stack[self.sp].take().unwrap())
    }

    fn pop_with_last(&mut self) -> Result<Object, VMError> {
        if self.sp == 0 {
            return Err(VMError::EmptyStack);
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
            const SUB: u8 = Opcode::Sub as u8;
            const MUL: u8 = Opcode::Mul as u8;
            const DIV: u8 = Opcode::Div as u8;
            const POP: u8 = Opcode::Pop as u8;
            const TRUE: u8 = Opcode::True as u8;
            const FALSE: u8 = Opcode::False as u8;
            const EQUAL: u8 = Opcode::Equal as u8;
            const NOT_EQUAL: u8 = Opcode::NotEqual as u8;
            const GREATER_THAN: u8 = Opcode::GreaterThan as u8;
            const MINUS: u8 = Opcode::Minus as u8;
            const BANG: u8 = Opcode::Bang as u8;

            match opcode {
                LOAD_CONSTANT => {
                    let constant_index = ((self.instructions[ip] as usize) << 8)
                        | (self.instructions[ip + 1] as usize);
                    ip += 2;

                    self.push(self.constants[constant_index].clone())?;
                }
                ADD => {
                    self.execute_binary_operation(opcode, |x, y| x + y)?;
                }
                SUB => {
                    self.execute_binary_operation(opcode, |x, y| x - y)?;
                }
                MUL => {
                    self.execute_binary_operation(opcode, |x, y| x * y)?;
                }
                DIV => {
                    self.execute_binary_operation(opcode, |x, y| x / y)?;
                }
                POP => {
                    self.pop_with_last()?;
                }
                TRUE => {
                    self.push(Object::Boolean(true))?;
                }
                FALSE => {
                    self.push(Object::Boolean(false))?;
                }
                EQUAL => {
                    let right = self.pop()?;
                    let left = self.pop()?;

                    match (&left, &right) {
                        (Object::Integer(l), Object::Integer(r)) => {
                            self.push(Object::Boolean(l == r))?;
                        }
                        (Object::Boolean(l), Object::Boolean(r)) => {
                            self.push(Object::Boolean(l == r))?;
                        }
                        _ => {
                            return Err(VMError::TypeMismatch {
                                left,
                                opcode: Opcode::try_from(opcode).unwrap(),
                                right,
                            });
                        }
                    };
                }
                NOT_EQUAL => {
                    let right = self.pop()?;
                    let left = self.pop()?;

                    match (&left, &right) {
                        (Object::Integer(l), Object::Integer(r)) => {
                            self.push(Object::Boolean(l != r))?;
                        }
                        (Object::Boolean(l), Object::Boolean(r)) => {
                            self.push(Object::Boolean(l != r))?;
                        }
                        _ => {
                            return Err(VMError::TypeMismatch {
                                left,
                                opcode: Opcode::try_from(opcode).unwrap(),
                                right,
                            });
                        }
                    };
                }
                GREATER_THAN => {
                    let right = self.pop()?;
                    let left = self.pop()?;

                    match (&left, &right) {
                        (Object::Integer(l), Object::Integer(r)) => {
                            self.push(Object::Boolean(l > r))?;
                        }
                        _ => {
                            return Err(VMError::TypeMismatch {
                                left,
                                opcode: Opcode::try_from(opcode).unwrap(),
                                right,
                            });
                        }
                    };
                }
                MINUS => {
                    self.execute_minus_operator()?;
                }
                BANG => {
                    self.execute_bang_operator()?;
                }

                _ => return Err(VMError::UnknownOpcode(opcode)),
            };
        }

        Ok(())
    }

    // Helpers

    #[inline(always)]
    fn execute_binary_operation<F>(&mut self, opcode: u8, op: F) -> Result<(), VMError>
    where
        F: Fn(i64, i64) -> i64,
    {
        let right = self.pop()?;
        let left = self.pop()?;

        match (&left, &right) {
            (Object::Integer(l), Object::Integer(r)) => {
                self.push(Object::Integer(op(*l, *r)))?;
                Ok(())
            }
            _ => Err(VMError::TypeMismatch {
                left,
                opcode: Opcode::try_from(opcode).unwrap(),
                right,
            }),
        }
    }

    fn execute_minus_operator(&mut self) -> Result<(), VMError> {
        let operand = self.pop()?;

        match operand {
            Object::Integer(value) => {
                self.push(Object::Integer(-value))?;
            }
            _ => {
                return Err(VMError::UnknownOperator {
                    operand: "-".to_string(),
                    right: operand,
                });
            }
        }

        Ok(())
    }

    fn execute_bang_operator(&mut self) -> Result<(), VMError> {
        let operand = self.pop()?;

        match operand {
            Object::Boolean(value) => {
                self.push(Object::Boolean(!value))?;
            }
            _ => self.push(Object::Boolean(false))?,
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
            VMTestCase {
                input: "1 - 2",
                expected: Object::Integer(-1),
            },
            VMTestCase {
                input: "4 / 2",
                expected: Object::Integer(2),
            },
            VMTestCase {
                input: "50 / 2 * 2 + 10 - 5",
                expected: Object::Integer(55),
            },
            VMTestCase {
                input: "5 + 5 + 5 + 5 - 10",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "2 * 2 * 2 * 2 * 2",
                expected: Object::Integer(32),
            },
            VMTestCase {
                input: "5 * 2 + 10",
                expected: Object::Integer(20),
            },
            VMTestCase {
                input: "5 + 2 * 10",
                expected: Object::Integer(25),
            },
            VMTestCase {
                input: "5 * (2 + 10)",
                expected: Object::Integer(60),
            },
            VMTestCase {
                input: "-5",
                expected: Object::Integer(-5),
            },
            VMTestCase {
                input: "-10",
                expected: Object::Integer(-10),
            },
            VMTestCase {
                input: "-50 + 100 + -50",
                expected: Object::Integer(0),
            },
            VMTestCase {
                input: "(5 + 10 * 2 + 15 / 3) * 2 + -10",
                expected: Object::Integer(50),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_boolean_expressions() -> Result<(), VMError> {
        let tests = vec![
            VMTestCase {
                input: "true",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "false",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "1 < 2",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "1 > 2",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "1 < 1",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "1 > 1",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "1 == 1",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "1 != 1",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "1 == 2",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "1 != 2",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "true == true",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "false == false",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "true == false",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "true != false",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "false != true",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "(1 < 2) == true",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "(1 < 2) == false",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "(1 > 2) == true",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "(1 > 2) == false",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "!true",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "!false",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "!5",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "!!true",
                expected: Object::Boolean(true),
            },
            VMTestCase {
                input: "!!false",
                expected: Object::Boolean(false),
            },
            VMTestCase {
                input: "!!5",
                expected: Object::Boolean(true),
            },
        ];

        run_vm_tests(&tests)
    }
}
