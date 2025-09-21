use std::collections::HashMap;

use crate::backend::code::Opcode;
use crate::backend::compiler::{Bytecode, Compiler};
use crate::runtime::object::{HashKey, Object};
use crate::runtime::vm::frame::Frame;

const STACK_SIZE: usize = 2048;
const GLOBAL_SIZE: usize = 65536;
const FRAMES_SIZE: usize = 1024;

#[allow(dead_code)]
#[derive(Debug)]
pub enum RuntimeError {
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
    UnboundIdentifier(usize),
    InvalidHashKey(Object),
    InvalidIndexType {
        indexable: Object,
        index: Object,
    },
    NotIndexable(Object),
    CallNonFunction(Object),
}

pub struct GlobalEnviroment {
    store: Box<[Option<Object>]>,
}

impl GlobalEnviroment {
    pub fn new() -> Self {
        let boxed: Box<[Option<Object>]> = vec![None; GLOBAL_SIZE].into_boxed_slice();
        GlobalEnviroment { store: boxed }
    }

    pub fn bind(&mut self, index: usize, object: Object) {
        self.store[index] = Some(object);
    }

    pub fn lookup(&self, index: usize) -> Result<&Object, RuntimeError> {
        self.store[index]
            .as_ref()
            .ok_or(RuntimeError::UnboundIdentifier(index))
    }

    pub fn get(&self, index: usize) -> Result<Object, RuntimeError> {
        match &self.store[index] {
            Some(value) => Ok(value.clone()),
            None => Err(RuntimeError::UnboundIdentifier(index)),
        }
    }
}

pub struct VM {
    constants: Box<[Object]>,

    pub stack: [Option<Object>; STACK_SIZE],
    sp: usize,

    last_popped: Object,
    pub globals: GlobalEnviroment,

    frames: [Option<Frame>; FRAMES_SIZE],
    frames_index: usize,
}

impl VM {
    pub fn new(bytecode: Bytecode) -> Self {
        let constants = bytecode.constants;
        let stack: [Option<Object>; STACK_SIZE] = std::array::from_fn(|_| None);
        let sp = 0;
        let last_popped = Object::Null;
        let globals = GlobalEnviroment::new();
        let mut frames: [Option<Frame>; FRAMES_SIZE] = std::array::from_fn(|_| None);
        frames[0] = Some(Frame::new(bytecode.instructions));
        let frames_index = 1;
        VM {
            constants: constants,
            stack: stack,
            sp: sp,
            last_popped: last_popped,
            globals: globals,
            frames: frames,
            frames_index: frames_index,
        }
    }

    pub fn new_with_global_store(bytecode: Bytecode, globals: GlobalEnviroment) -> Self {
        let mut vm = VM::new(bytecode);
        vm.globals = globals;
        vm
    }

    pub fn stack_top(&self) -> Result<&Object, RuntimeError> {
        if self.sp == 0 {
            Err(RuntimeError::EmptyStack)
        } else {
            Ok(&self.stack[self.sp - 1].as_ref().unwrap())
        }
    }

    fn push(&mut self, object: Object) -> Result<(), RuntimeError> {
        if self.sp == STACK_SIZE {
            return Err(RuntimeError::StackOverflow);
        }

        self.stack[self.sp] = Some(object);
        self.sp += 1;

        Ok(())
    }

    fn pop(&mut self) -> Object {
        debug_assert!(self.sp > 0, "VM bug: attempted to pop from empty stack");

        self.sp -= 1;
        self.stack[self.sp].take().unwrap()
    }

    fn pop_with_last(&mut self) -> Result<Object, RuntimeError> {
        if self.sp == 0 {
            return Err(RuntimeError::EmptyStack);
        }

        self.sp -= 1;
        self.last_popped = self.stack[self.sp].clone().unwrap();
        Ok(self.stack[self.sp].take().unwrap())
    }

    pub fn last_popped_stack_element(&self) -> &Object {
        &self.last_popped
    }

    fn current_frame(&self) -> &Frame {
        self.frames[self.frames_index - 1]
            .as_ref()
            .expect("no current frame")
    }

    fn current_frame_mut(&mut self) -> &mut Frame {
        self.frames[self.frames_index - 1]
            .as_mut()
            .expect("no current frame")
    }

    fn push_frame(&mut self, frame: Frame) {
        self.frames[self.frames_index] = Some(frame);
        self.frames_index += 1;
    }

    fn pop_frame(&mut self) -> Frame {
        self.frames_index -= 1;
        let frame = self.frames[self.frames_index]
            .take()
            .expect("no frame to pop");
        frame
    }

    pub fn run(&mut self) -> Result<(), RuntimeError> {
        while self.current_frame().ip < self.current_frame().function.len() {
            let current_frame = self.current_frame_mut();
            let opcode = current_frame.function[current_frame.ip];
            current_frame.ip += 1;

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
            const JUMP_NOT_TRUTHY: u8 = Opcode::JumpNotTruthy as u8;
            const JUMP: u8 = Opcode::Jump as u8;
            const NULL: u8 = Opcode::Null as u8;
            const GET_GLOBAL: u8 = Opcode::GetGlobal as u8;
            const SET_GLOBAL: u8 = Opcode::SetGlobal as u8;
            const ARRAY: u8 = Opcode::Array as u8;
            const HASH: u8 = Opcode::Hash as u8;
            const INDEX: u8 = Opcode::Index as u8;
            const CALL: u8 = Opcode::Call as u8;
            const RETURN_VALUE: u8 = Opcode::ReturnValue as u8;
            const RETURN: u8 = Opcode::Return as u8;

            match opcode {
                LOAD_CONSTANT => {
                    let constant_index = ((current_frame.function[current_frame.ip] as usize) << 8)
                        | (current_frame.function[current_frame.ip + 1] as usize);
                    current_frame.ip += 2;

                    self.push(self.constants[constant_index].clone())?;
                }
                ADD => {
                    let right = self.pop();
                    let left = self.pop();

                    match (&left, &right) {
                        (Object::Integer(l), Object::Integer(r)) => {
                            self.push(Object::Integer(*l + *r))?;
                        }
                        (Object::String(l), Object::String(r)) => {
                            self.push(Object::String(format!("{}{}", l, r).to_string()))?;
                        }
                        _ => {
                            return Err(RuntimeError::TypeMismatch {
                                left,
                                opcode: Opcode::from_byte(opcode),
                                right,
                            });
                        }
                    };
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
                    let right = self.pop();
                    let left = self.pop();

                    match (&left, &right) {
                        (Object::Integer(l), Object::Integer(r)) => {
                            self.push(Object::Boolean(l == r))?;
                        }
                        (Object::Boolean(l), Object::Boolean(r)) => {
                            self.push(Object::Boolean(l == r))?;
                        }
                        _ => {
                            return Err(RuntimeError::TypeMismatch {
                                left,
                                opcode: Opcode::from_byte(opcode),
                                right,
                            });
                        }
                    };
                }
                NOT_EQUAL => {
                    let right = self.pop();
                    let left = self.pop();

                    match (&left, &right) {
                        (Object::Integer(l), Object::Integer(r)) => {
                            self.push(Object::Boolean(l != r))?;
                        }
                        (Object::Boolean(l), Object::Boolean(r)) => {
                            self.push(Object::Boolean(l != r))?;
                        }
                        _ => {
                            return Err(RuntimeError::TypeMismatch {
                                left,
                                opcode: Opcode::from_byte(opcode),
                                right,
                            });
                        }
                    };
                }
                GREATER_THAN => {
                    let right = self.pop();
                    let left = self.pop();

                    match (&left, &right) {
                        (Object::Integer(l), Object::Integer(r)) => {
                            self.push(Object::Boolean(l > r))?;
                        }
                        _ => {
                            return Err(RuntimeError::TypeMismatch {
                                left,
                                opcode: Opcode::from_byte(opcode),
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
                JUMP_NOT_TRUTHY => {
                    let position = {
                        let frame = self.current_frame_mut();
                        let pos = ((frame.function[frame.ip] as usize) << 8)
                            | (frame.function[frame.ip + 1] as usize);
                        frame.ip += 2;
                        pos
                    };

                    let condition = self.pop();
                    if !Self::is_truthy(&condition) {
                        self.current_frame_mut().ip = position;
                    }
                }
                JUMP => {
                    let position = ((current_frame.function[current_frame.ip] as usize) << 8)
                        | (current_frame.function[current_frame.ip + 1] as usize);
                    current_frame.ip = position;
                }
                NULL => {
                    self.push(Object::Null)?;
                }
                GET_GLOBAL => {
                    let global_index = u16::from_be_bytes(
                        current_frame.function[current_frame.ip..current_frame.ip + 2]
                            .try_into()
                            .unwrap(),
                    ) as usize;
                    current_frame.ip += 2;

                    self.push(self.globals.get(global_index)?)?;
                }
                SET_GLOBAL => {
                    let global_index = u16::from_be_bytes(
                        current_frame.function[current_frame.ip..current_frame.ip + 2]
                            .try_into()
                            .unwrap(),
                    ) as usize;
                    current_frame.ip += 2;

                    let global = self.pop_with_last()?;
                    self.globals.bind(global_index, global);
                }
                ARRAY => {
                    let array_length = u16::from_be_bytes(
                        current_frame.function[current_frame.ip..current_frame.ip + 2]
                            .try_into()
                            .unwrap(),
                    ) as usize;
                    current_frame.ip += 2;

                    if self.sp < array_length {
                        return Err(RuntimeError::EmptyStack);
                    }

                    let start = self.sp - array_length;
                    let array: Vec<Object> = self.stack[start..self.sp]
                        .iter_mut()
                        .map(|opt| opt.take().unwrap())
                        .collect();

                    self.sp -= array_length;

                    self.push(Object::Array(array))?;
                }
                HASH => {
                    let hash_length = u16::from_be_bytes(
                        current_frame.function[current_frame.ip..current_frame.ip + 2]
                            .try_into()
                            .unwrap(),
                    ) as usize;
                    current_frame.ip += 2;

                    if self.sp < hash_length {
                        return Err(RuntimeError::EmptyStack);
                    }

                    let start = self.sp - hash_length;
                    let mut hash = HashMap::<HashKey, Object>::with_capacity(hash_length / 2);

                    let mut i = start;
                    while i < hash_length {
                        let key = match self.stack[i].take().unwrap() {
                            Object::Integer(value) => HashKey::Integer(value),
                            Object::String(value) => HashKey::String(value),
                            other => return Err(RuntimeError::InvalidHashKey(other)),
                        };
                        let value = self.stack[i + 1].take().unwrap();

                        hash.insert(key, value);

                        i += 2;
                    }

                    self.sp -= hash_length;
                    self.push(Object::Hash(hash))?;
                }
                INDEX => {
                    let index_object = self.pop();
                    let indexable_object = self.pop();

                    match &indexable_object {
                        Object::Array(array) => {
                            let index = match index_object {
                                Object::Integer(value) => value,
                                other => {
                                    return Err(RuntimeError::InvalidIndexType {
                                        indexable: indexable_object,
                                        index: other,
                                    });
                                }
                            };

                            match array.get(index as usize) {
                                Some(obj) => self.push(obj.clone())?,
                                None => self.push(Object::Null)?,
                            }
                        }
                        Object::Hash(hash) => {
                            let key = match index_object {
                                Object::Integer(value) => HashKey::Integer(value),
                                Object::String(value) => HashKey::String(value),
                                other => {
                                    return Err(RuntimeError::InvalidIndexType {
                                        indexable: indexable_object,
                                        index: other,
                                    });
                                }
                            };

                            if let Some(value) = hash.get(&key) {
                                self.push(value.clone())?;
                            } else {
                                self.push(Object::Null)?;
                            }
                        }
                        other => return Err(RuntimeError::NotIndexable(other.clone())),
                    }
                }
                CALL => {
                    match self.stack[self.sp - 1].as_ref().unwrap().clone() {
                        Object::CompiledFunction(function) => {
                            let frame = Frame::new(function.instructions);
                            self.push_frame(frame);
                            // comment is just here now to not make the formatting freak out
                        }
                        other => {
                            return Err(RuntimeError::CallNonFunction(other));
                        }
                    }
                }
                RETURN_VALUE => {
                    let return_value = self.pop();

                    self.pop_frame();
                    self.pop();

                    self.push(return_value)?;
                }
                RETURN => {
                    self.pop_frame();
                    self.pop();
                    self.push(Object::Null)?;
                }
                _ => return Err(RuntimeError::UnknownOpcode(opcode)),
            };
        }

        Ok(())
    }

    // Helpers

    #[inline(always)]
    fn execute_binary_operation<F>(&mut self, opcode: u8, op: F) -> Result<(), RuntimeError>
    where
        F: Fn(i64, i64) -> i64,
    {
        let right = self.pop();
        let left = self.pop();

        match (&left, &right) {
            (Object::Integer(l), Object::Integer(r)) => {
                self.push(Object::Integer(op(*l, *r)))?;
                Ok(())
            }
            _ => Err(RuntimeError::TypeMismatch {
                left,
                opcode: Opcode::from_byte(opcode),
                right,
            }),
        }
    }

    fn execute_minus_operator(&mut self) -> Result<(), RuntimeError> {
        let operand = self.pop();

        match operand {
            Object::Integer(value) => {
                self.push(Object::Integer(-value))?;
            }
            _ => {
                return Err(RuntimeError::UnknownOperator {
                    operand: "-".to_string(),
                    right: operand,
                });
            }
        }

        Ok(())
    }

    fn execute_bang_operator(&mut self) -> Result<(), RuntimeError> {
        let operand = self.pop();

        let result: Object = match operand {
            Object::Boolean(value) => Object::Boolean(!value),
            Object::Null => Object::Boolean(true),
            _ => Object::Boolean(false),
        };

        self.push(result)?;

        Ok(())
    }

    fn is_truthy(object: &Object) -> bool {
        match object {
            Object::Boolean(value) => *value,
            Object::Null => false,
            _ => true,
        }
    }
}

#[cfg(test)]
mod tests {

    use std::collections::HashMap;

    use super::*;
    use crate::{
        frontend::ast::Program, frontend::lexer::Lexer, frontend::parser::Parser,
        runtime::object::HashKey,
    };

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

    fn run_vm_tests(tests: &[VMTestCase]) -> Result<(), RuntimeError> {
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
    fn test_integer_arithmetic() -> Result<(), RuntimeError> {
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
    fn test_boolean_expressions() -> Result<(), RuntimeError> {
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
            VMTestCase {
                input: "!(if (false) { 5; })",
                expected: Object::Boolean(true),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_conditionals() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "if (true) { 10 }",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "if (true) { 10 } else { 20 }",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "if (false) { 10 } else { 20 } ",
                expected: Object::Integer(20),
            },
            VMTestCase {
                input: "if (1) { 10 }",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "if (1 < 2) { 10 }",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "if (1 < 2) { 10 } else { 20 }",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "if (1 > 2) { 10 } else { 20 }",
                expected: Object::Integer(20),
            },
            VMTestCase {
                input: "if (1 > 2) { 10 }",
                expected: Object::Null,
            },
            VMTestCase {
                input: "if (false) { 10 }",
                expected: Object::Null,
            },
            VMTestCase {
                input: "if ((if (false) { 10 })) { 10 } else { 20 }",
                expected: Object::Integer(20),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_global_let_statements() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "let one = 1; one;",
                expected: Object::Integer(1),
            },
            VMTestCase {
                input: "let one = 1; let two = 2; one + two",
                expected: Object::Integer(3),
            },
            VMTestCase {
                input: "let one = 1; let two = one + one; one + two",
                expected: Object::Integer(3),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_string_expressions() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "\"monkey\"",
                expected: Object::String("monkey".to_string()),
            },
            VMTestCase {
                input: "\"mon\" + \"key\"",
                expected: Object::String("monkey".to_string()),
            },
            VMTestCase {
                input: "\"mon\" + \"key\" + \"banana\"",
                expected: Object::String("monkeybanana".to_string()),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_array_literals() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "[]",
                expected: Object::Array(vec![]),
            },
            VMTestCase {
                input: "[1, 2, 3]",
                expected: Object::Array(vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                ]),
            },
            VMTestCase {
                input: "[1 + 2, 3 * 4, 5 + 6]",
                expected: Object::Array(vec![
                    Object::Integer(3),
                    Object::Integer(12),
                    Object::Integer(11),
                ]),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_hash_literals() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "{}",
                expected: Object::Hash(HashMap::<HashKey, Object>::new()),
            },
            VMTestCase {
                input: "{1: 2, 2: 3}",
                expected: Object::Hash(HashMap::from([
                    (HashKey::Integer(1), Object::Integer(2)),
                    (HashKey::Integer(2), Object::Integer(3)),
                ])),
            },
            VMTestCase {
                input: "{1 + 1: 2 * 2, 3 + 3: 4 * 4}",
                expected: Object::Hash(HashMap::from([
                    (HashKey::Integer(2), Object::Integer(4)),
                    (HashKey::Integer(6), Object::Integer(16)),
                ])),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_index_expressions() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "[1, 2, 3][0 + 2]",
                expected: Object::Integer(3),
            },
            VMTestCase {
                input: "[[1, 1, 1]][0][0]",
                expected: Object::Integer(1),
            },
            VMTestCase {
                input: "[][0]",
                expected: Object::Null,
            },
            VMTestCase {
                input: "[1, 2, 3][99]",
                expected: Object::Null,
            },
            VMTestCase {
                input: "[1][-1]",
                expected: Object::Null,
            },
            VMTestCase {
                input: "{1: 1, 2: 2}[1]",
                expected: Object::Integer(1),
            },
            VMTestCase {
                input: "{1: 1, 2: 2}[2]",
                expected: Object::Integer(2),
            },
            VMTestCase {
                input: "{1: 1}[0]",
                expected: Object::Null,
            },
            VMTestCase {
                input: "{}[0]",
                expected: Object::Null,
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_calling_functions_without_arguments() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "let fivePlusTen = fn() { 5 + 10; };
                        fivePlusTen();",
                expected: Object::Integer(15),
            },
            VMTestCase {
                input: "let one = fn() { 1; };
                        let two = fn() { 2; };
                        one() + two()",
                expected: Object::Integer(3),
            },
            VMTestCase {
                input: "let a = fn() { 1 };
                        let b = fn() { a() + 1 };
                        let c = fn() { b() + 1 };
                        c();",
                expected: Object::Integer(3),
            },
        ];

        run_vm_tests(&tests)
    }


    #[test]
    fn test_calling_functions_with_bindings() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "let one = fn() { let one = 1; one };
                        one();",
                expected: Object::Integer(1),
            },
            VMTestCase {
                input: "let oneAndTwo = fn() { let one = 1; let two = 2; one + two; };
                        oneAndTwo();",
                expected: Object::Integer(3),
            },
            VMTestCase {
                input: "let oneAndTwo = fn() { let one = 1; let two = 2; one + two; };
                        let threeAndFour = fn() { let three = 3; let four = 4; three + four; };
                        oneAndTwo() + threeAndFour();",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "let firstFoobar = fn() { let foobar = 50; foobar; };
                        let secondFoobar = fn() { let foobar = 100; foobar; };
                        firstFoobar() + secondFoobar();",
                expected: Object::Integer(150),
            },
            VMTestCase {
                input: "let globalSeed = 50;
                        let minusOne = fn() {
                            let num = 1;
                            globalSeed - num;
                        }
                        let minusTwo = fn() {
                            let num = 2;
                            globalSeed - num;
                        }
                        minusOne() + minusTwo();",
                expected: Object::Integer(97),
            },
        ];

        run_vm_tests(&tests)
    }


    #[test]
    fn test_functions_with_return_statement() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "let earlyExit = fn() { return 99; 100; };
                        earlyExit();",
                expected: Object::Integer(99),
            },
            VMTestCase {
                input: "let earlyExit = fn() { return 99; return 100; };
                        earlyExit();",
                expected: Object::Integer(99),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_functions_without_return_value() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "let noReturn = fn() { };
                        noReturn();",
                expected: Object::Null,
            },
            VMTestCase {
                input: "let noReturn = fn() { };
                        let noReturnTwo = fn() { noReturn(); };
                        noReturn();
                        noReturnTwo();",
                expected: Object::Null,
            },
        ];

        run_vm_tests(&tests)
    }
}
