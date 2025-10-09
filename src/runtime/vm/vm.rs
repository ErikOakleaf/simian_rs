use std::cell::RefCell;
use std::collections::HashMap;
use std::mem::MaybeUninit;
use std::rc::Rc;

use crate::backend::code::Opcode;
use crate::backend::compiler::Bytecode;
use crate::runtime::builtins::BUILTINS;
use crate::runtime::object::{BuiltinFunction, Closure, CompiledFunction, HashKey, Object};
use crate::runtime::vm::frame::Frame;

const STACK_SIZE: usize = 2048;
const GLOBAL_SIZE: usize = 65536;
const FRAMES_SIZE: usize = 1024;

#[derive(Debug, PartialEq)]
pub enum RuntimeError {
    EmptyStack,
    StackOverflow,
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
    ArityMismatch {
        expected: usize,
        got: usize,
    },
    Other(String),
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

    pub fn get(&self, index: usize) -> Result<Object, RuntimeError> {
        match &self.store[index] {
            Some(value) => Ok(value.clone()),
            None => Err(RuntimeError::UnboundIdentifier(index)),
        }
    }
}

pub struct VM {
    constants: Box<[Object]>,

    pub stack: [MaybeUninit<Object>; STACK_SIZE],
    sp: usize,

    last_popped: Object,
    pub globals: GlobalEnviroment,

    frames: [Option<Frame>; FRAMES_SIZE],
    frames_index: usize,
}

impl VM {
    pub fn new(bytecode: Bytecode) -> Self {
        let constants = bytecode.constants;
        let stack = unsafe { MaybeUninit::uninit().assume_init() };
        let sp = 0;
        let last_popped = Object::Null;
        let globals = GlobalEnviroment::new();
        let mut frames: [Option<Frame>; FRAMES_SIZE] = std::array::from_fn(|_| None);

        let main_function = Rc::new(CompiledFunction::new(bytecode.instructions, 0, 0));
        let main_closure = Closure::new(main_function, Box::new([]));

        frames[0] = Some(Frame::new(Rc::new(main_closure), 0));
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

    #[inline]
    fn push(&mut self, object: Object) -> Result<(), RuntimeError> {
        if self.sp == STACK_SIZE {
            return Err(RuntimeError::StackOverflow);
        }

        self.stack[self.sp] = MaybeUninit::new(object);
        self.sp += 1;

        Ok(())
    }

    #[inline]
    fn pop(&mut self) -> Object {
        debug_assert!(self.sp > 0, "VM bug: attempted to pop from empty stack");

        self.sp -= 1;
        unsafe { self.stack[self.sp].assume_init_read() }
    }

    #[inline]
    fn pop_with_last(&mut self) -> Result<Object, RuntimeError> {
        debug_assert!(self.sp > 0, "VM bug: attempted to pop from empty stack");

        self.sp -= 1;
        let popped = unsafe { self.stack[self.sp].assume_init_read() };

        self.last_popped = popped.clone();
        Ok(popped)
    }

    #[inline(always)]
    pub fn last_popped_stack_element(&self) -> &Object {
        &self.last_popped
    }

    #[inline]
    fn push_frame(&mut self, frame: Frame) {
        self.frames[self.frames_index] = Some(frame);
        self.frames_index += 1;
    }

    #[inline]
    fn pop_frame(&mut self) -> Frame {
        self.frames_index -= 1;
        let frame = self.frames[self.frames_index]
            .take()
            .expect("no frame to pop");
        frame
    }

    fn push_closure(&mut self, const_index: usize, amount_free: usize) -> Result<(), RuntimeError> {
        let constant = self.constants[const_index].clone();
        let function = match constant {
            Object::CompiledFunction(compiled_function) => compiled_function,
            _ => unreachable!("pushed non closure in push closure"),
        };

        let base = self.current_frame().base_pointer;
        let mut free_variables = Vec::<Object>::with_capacity(amount_free);
        for _ in 0..amount_free {
            let flag = self.read_byte();
            let index = self.read_byte() as usize;

            if flag == 0 {
                let slot = base + index;

                let existing = unsafe { self.stack[slot].assume_init_read() };

                let cell = match existing {
                    Object::Cell(cell) => cell,
                    other => Rc::new(RefCell::new(other)),
                };

                self.stack[slot].write(Object::Cell(cell.clone()));

                free_variables.push(Object::Cell(cell));
            } else if flag == 1 {
                let free = self.current_frame().closure.as_ref().free[index].clone();
                free_variables.push(free);
            }
        }

        let closure = Rc::new(Closure::new(
            function.clone(),
            free_variables.into_boxed_slice(),
        ));
        self.push(Object::Closure(closure))?;

        Ok(())
    }

    pub fn run(&mut self) -> Result<(), RuntimeError> {
        while self.current_frame().ip < self.current_frame().instructions().len() {
            let current_frame = self.current_frame_mut();
            let opcode = current_frame.instructions()[current_frame.ip];
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
            const GET_LOCAL: u8 = Opcode::GetLocal as u8;
            const SET_LOCAL: u8 = Opcode::SetLocal as u8;
            const GET_BUILTIN: u8 = Opcode::GetBuiltin as u8;
            const CLOSURE: u8 = Opcode::Closure as u8;
            const GET_FREE: u8 = Opcode::GetFree as u8;
            const CURRENT_CLOSURE: u8 = Opcode::CurrentClosure as u8;
            const ASSIGN_INDEXABLE: u8 = Opcode::AssignIndexable as u8;
            const ASSIGN_FREE: u8 = Opcode::AssignFree as u8;

            match opcode {
                LOAD_CONSTANT => {
                    let constant_index =
                        ((current_frame.instructions()[current_frame.ip] as usize) << 8)
                            | (current_frame.instructions()[current_frame.ip + 1] as usize);
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
                        (Object::Float(l), Object::Float(r)) => {
                            self.push(Object::Float(*l + *r))?;
                        }
                        (Object::Float(l), Object::Integer(r)) => {
                            self.push(Object::Float(*l + *r as f64))?;
                        }
                        (Object::Integer(l), Object::Float(r)) => {
                            self.push(Object::Float(*l as f64 + *r))?;
                        }
                        (Object::String(l), Object::String(r)) => {
                            self.push(Object::String(Rc::new(RefCell::new(
                                format!("{}{}", l.borrow(), r.borrow()).to_string(),
                            ))))?;
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
                    self.execute_binary_operation(opcode, |x, y| x - y, |x, y| x - y)?;
                }
                MUL => {
                    self.execute_binary_operation(opcode, |x, y| x * y, |x, y| x * y)?;
                }
                DIV => {
                    self.execute_binary_operation(opcode, |x, y| x / y, |x, y| x / y)?;
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
                        let pos = ((frame.instructions()[frame.ip] as usize) << 8)
                            | (frame.instructions()[frame.ip + 1] as usize);
                        frame.ip += 2;
                        pos
                    };

                    let condition = self.pop();
                    if !Self::is_truthy(&condition) {
                        self.current_frame_mut().ip = position;
                    }
                }
                JUMP => {
                    let position = ((current_frame.instructions()[current_frame.ip] as usize) << 8)
                        | (current_frame.instructions()[current_frame.ip + 1] as usize);
                    current_frame.ip = position;
                }
                NULL => {
                    self.push(Object::Null)?;
                }
                GET_GLOBAL => {
                    let global_index = self.read_2_bytes() as usize;

                    self.push(self.globals.get(global_index)?)?;
                }
                SET_GLOBAL => {
                    let global_index = self.read_2_bytes() as usize;

                    let global = self.pop_with_last()?;
                    self.globals.bind(global_index, global);
                }
                ARRAY => {
                    let array_length = self.read_2_bytes() as usize;

                    if self.sp < array_length {
                        return Err(RuntimeError::EmptyStack);
                    }

                    let start = self.sp - array_length;

                    let mut array = Vec::with_capacity(array_length);
                    for i in start..self.sp {
                        unsafe {
                            array.push(self.stack[i].assume_init_read());
                        }
                    }

                    self.sp = start;

                    self.push(Object::Array(Rc::new(RefCell::new(array))))?;
                }
                HASH => {
                    let hash_length = self.read_2_bytes() as usize;

                    if self.sp < hash_length {
                        return Err(RuntimeError::EmptyStack);
                    }

                    let start = self.sp - hash_length;
                    let mut hash = HashMap::<HashKey, Object>::with_capacity(hash_length / 2);

                    let mut i = start;
                    while i < hash_length {
                        let key = match unsafe { self.stack[i].assume_init_read() } {
                            Object::Integer(value) => HashKey::Integer(value),
                            Object::Boolean(value) => HashKey::Boolean(value),
                            Object::String(value) => HashKey::String(value.borrow().to_string()),
                            other => return Err(RuntimeError::InvalidHashKey(other)),
                        };
                        let value = unsafe { self.stack[i + 1].assume_init_read() };

                        hash.insert(key, value);

                        i += 2;
                    }

                    self.sp -= hash_length;
                    self.push(Object::Hash(Rc::new(RefCell::new(hash))))?;
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

                            match array.borrow().get(index as usize) {
                                Some(obj) => self.push(obj.clone())?,
                                None => self.push(Object::Null)?,
                            }
                        }
                        Object::Hash(hash) => {
                            let key = match index_object {
                                Object::Integer(value) => HashKey::Integer(value),
                                Object::Boolean(value) => HashKey::Boolean(value),
                                Object::String(value) => {
                                    HashKey::String(value.borrow().to_string())
                                }
                                other => {
                                    return Err(RuntimeError::InvalidIndexType {
                                        indexable: indexable_object,
                                        index: other,
                                    });
                                }
                            };

                            if let Some(value) = hash.borrow().get(&key) {
                                self.push(value.clone())?;
                            } else {
                                self.push(Object::Null)?;
                            }
                        }
                        Object::String(string) => {
                            let index = match index_object {
                                Object::Integer(value) => value as usize,
                                other => {
                                    return Err(RuntimeError::InvalidIndexType {
                                        indexable: indexable_object,
                                        index: other,
                                    });
                                }
                            };

                            let string_char = string.borrow().chars().nth(index);
                            match string_char {
                                Some(value) => self.push(Object::Char(value))?,
                                None => self.push(Object::Null)?,
                            };
                        }
                        other => return Err(RuntimeError::NotIndexable(other.clone())),
                    }
                }
                CALL => {
                    let amount_arguments = self.read_byte() as usize;

                    self.execute_call(amount_arguments)?;
                }
                RETURN_VALUE => {
                    let return_value = self.pop();

                    let frame = self.pop_frame();
                    self.sp = frame.base_pointer - 1;

                    self.push(return_value)?;
                }
                RETURN => {
                    let frame = self.pop_frame();
                    self.sp = frame.base_pointer - 1;

                    self.push(Object::Null)?;
                }
                GET_LOCAL => {
                    let local_index;
                    let base_pointer;
                    {
                        let current_frame = self.current_frame_mut();
                        local_index = current_frame.instructions()[current_frame.ip] as usize;
                        current_frame.ip += 1;
                        base_pointer = current_frame.base_pointer;
                    }

                    let value = unsafe { &*self.stack[base_pointer + local_index].as_ptr() };

                    let object = match value {
                        Object::Cell(cell) => cell.borrow().clone(),
                        other => other.clone(),
                    };

                    self.push(object)?;
                }
                SET_LOCAL => {
                    let local_index;
                    let base_pointer;
                    {
                        let current_frame = self.current_frame_mut();
                        local_index = current_frame.instructions()[current_frame.ip] as usize;
                        current_frame.ip += 1;
                        base_pointer = current_frame.base_pointer;
                    }

                    let value = self.pop();
                    self.stack[base_pointer + local_index] = MaybeUninit::new(value);
                }
                GET_BUILTIN => {
                    let builtin_index = self.read_byte() as usize;

                    let definiton = Object::Builtin(&BUILTINS[builtin_index]);
                    self.push(definiton)?;
                }
                CLOSURE => {
                    let const_index = self.read_2_bytes() as usize;
                    let amount_free = self.read_byte() as usize;

                    self.push_closure(const_index, amount_free)?;
                }
                GET_FREE => {
                    let object = {
                        let frame = self.current_frame_mut();
                        let free_index = frame.instructions()[frame.ip];
                        frame.ip += 1;
                        let cell_object = frame.closure.free[free_index as usize].clone();
                        let cell = match cell_object {
                            Object::Cell(cell) => cell,
                            _ => unreachable!("non cell free variable"),
                        };

                        cell.borrow().clone()
                    };

                    self.push(object)?;
                }
                CURRENT_CLOSURE => {
                    let current_closure = self.current_frame().closure.clone();
                    self.push(Object::Closure(current_closure))?;
                }
                ASSIGN_INDEXABLE => {
                    let value = self.pop();
                    let index_object = self.pop();
                    let container = self.pop_with_last()?;

                    match &container {
                        Object::Array(arr) => {
                            let index = match index_object {
                                Object::Integer(value) => value,
                                other => {
                                    return Err(RuntimeError::InvalidIndexType {
                                        indexable: container.clone(),
                                        index: other,
                                    });
                                }
                            };
                            arr.borrow_mut()[index as usize] = value;
                        }
                        Object::Hash(hash) => {
                            let key = match index_object {
                                Object::Integer(value) => HashKey::Integer(value),
                                Object::Boolean(value) => HashKey::Boolean(value),
                                Object::String(value) => {
                                    HashKey::String(value.borrow().to_string())
                                }
                                other => {
                                    return Err(RuntimeError::InvalidIndexType {
                                        indexable: container.clone(),
                                        index: other,
                                    });
                                }
                            };

                            hash.borrow_mut().insert(key, value);
                        }
                        other => return Err(RuntimeError::NotIndexable(other.clone())),
                    }
                }
                ASSIGN_FREE => {
                    let (free_index, value) = {
                        let frame = self.current_frame_mut();
                        let free_index = frame.instructions()[frame.ip];
                        frame.ip += 1;
                        let value = self.pop();
                        (free_index, value)
                    };

                    let cell_object =
                        self.current_frame().closure.free[free_index as usize].clone();
                    let cell = match cell_object {
                        Object::Cell(cell) => cell,
                        _ => unreachable!("non cell free variable"),
                    };

                    *cell.borrow_mut() = value;
                }
                other => unreachable!("Unkown opcode {}", other),
            };
        }

        Ok(())
    }

    // Helpers

    fn execute_call(&mut self, amount_arguments: usize) -> Result<(), RuntimeError> {
        let callee_slot = &self.stack[self.sp - 1 - amount_arguments];
        let callee = unsafe { &*callee_slot.as_ptr() };

        match callee {
            Object::Closure(closure) => self.call_closure(closure.clone(), amount_arguments),
            Object::Builtin(builtin_function) => {
                self.call_builtin(builtin_function, amount_arguments)
            }
            other => {
                return Err(RuntimeError::CallNonFunction(other.clone()));
            }
        }
    }

    fn call_closure(
        &mut self,
        closure: Rc<Closure>,
        amount_arguments: usize,
    ) -> Result<(), RuntimeError> {
        if amount_arguments != closure.function.amount_parameters {
            return Err(RuntimeError::ArityMismatch {
                expected: closure.function.amount_parameters,
                got: amount_arguments,
            });
        }

        let amount_locals = closure.function.amount_locals;
        let frame = Frame::new(closure, self.sp - amount_arguments);

        self.sp = frame.base_pointer + amount_locals;
        self.push_frame(frame);
        Ok(())
    }

    fn call_builtin(
        &mut self,
        builtin: &BuiltinFunction,
        amount_arguments: usize,
    ) -> Result<(), RuntimeError> {
        let start = self.sp - amount_arguments;
        let arguments: Vec<Object> = self.stack[start..self.sp]
            .iter()
            .map(|arg| unsafe { arg.assume_init_read() })
            .collect();

        let result = (builtin.func)(&arguments)?;
        self.sp = start;
        self.push(result)?;
        Ok(())
    }

    #[inline]
    fn execute_binary_operation<FI, FF>(
        &mut self,
        opcode: u8,
        op_int: FI,
        op_float: FF,
    ) -> Result<(), RuntimeError>
    where
        FI: Fn(i64, i64) -> i64 + Copy,
        FF: Fn(f64, f64) -> f64 + Copy,
    {
        let right = self.pop();
        let left = self.pop();

        match (left, right) {
            (Object::Integer(l), Object::Integer(r)) => self.push(Object::Integer(op_int(l, r))),
            (Object::Float(l), Object::Float(r)) => self.push(Object::Float(op_float(l, r))),
            (Object::Integer(l), Object::Float(r)) => {
                self.push(Object::Float(op_float(l as f64, r)))
            }
            (Object::Float(l), Object::Integer(r)) => {
                self.push(Object::Float(op_float(l, r as f64)))
            }
            (l, r) => Err(RuntimeError::TypeMismatch {
                left: l,
                opcode: Opcode::from_byte(opcode),
                right: r,
            }),
        }
    }

    fn execute_minus_operator(&mut self) -> Result<(), RuntimeError> {
        let operand = self.pop();

        match operand {
            Object::Integer(value) => {
                self.push(Object::Integer(-value))?;
            }
            Object::Float(value) => {
                self.push(Object::Float(-value))?;
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

    #[inline(always)]
    fn current_frame(&self) -> &Frame {
        self.frames[self.frames_index - 1]
            .as_ref()
            .expect("no current frame")
    }

    #[inline(always)]
    fn current_frame_mut(&mut self) -> &mut Frame {
        self.frames[self.frames_index - 1]
            .as_mut()
            .expect("no current frame")
    }

    #[inline(always)]
    fn read_byte(&mut self) -> u8 {
        let current_frame = self.current_frame_mut();
        let byte = current_frame.instructions()[current_frame.ip];
        current_frame.ip += 1;
        byte
    }

    #[inline(always)]
    fn read_2_bytes(&mut self) -> u16 {
        let current_frame = self.current_frame_mut();
        let bytes = u16::from_be_bytes(
            current_frame.instructions()[current_frame.ip..current_frame.ip + 2]
                .try_into()
                .unwrap(),
        );
        current_frame.ip += 2;
        bytes
    }
}

#[cfg(test)]
mod tests {

    use crate::backend::compiler::Compiler;
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
        let chars: Vec<char> = input.chars().collect();
        let mut parser = Parser::new(&chars);
        parser.parse_program().unwrap()
    }

    fn run_vm_tests(tests: &[VMTestCase]) -> Result<(), RuntimeError> {
        for test in tests {
            let program = parse_input(test.input);
            let chars : Vec<char> = test.input.chars().collect();
            let mut compiler = Compiler::new(&chars);
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
    fn test_float_arithmetic() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "1.11",
                expected: Object::Float(1.11),
            },
            VMTestCase {
                input: "2.22",
                expected: Object::Float(2.22),
            },
            VMTestCase {
                input: "1.11 + 2.22",
                expected: Object::Float(3.33),
            },
            VMTestCase {
                input: "1.1 - 2.2",
                expected: Object::Float(-1.1),
            },
            VMTestCase {
                input: "5.0 / 2",
                expected: Object::Float(2.5),
            },
            VMTestCase {
                input: "51 / 2.0 * 2 + 10 - 5.5",
                expected: Object::Float(55.5),
            },
            VMTestCase {
                input: "5.5 + 5.2 + 5.2 + 5 - 10.1238",
                expected: Object::Float(10.7762),
            },
            VMTestCase {
                input: "2.5 * 2 * 2 * 2 * 2",
                expected: Object::Float(40 as f64),
            },
            VMTestCase {
                input: "5.3 * 2 + 10",
                expected: Object::Float(20.6),
            },
            VMTestCase {
                input: "5 + 2.7 * 10",
                expected: Object::Float(32 as f64),
            },
            VMTestCase {
                input: "5 * (2 + 10.1)",
                expected: Object::Float(60.5),
            },
            VMTestCase {
                input: "-5.8",
                expected: Object::Float(-5.8),
            },
            VMTestCase {
                input: "-10.283",
                expected: Object::Float(-10.283),
            },
            VMTestCase {
                input: "-50.8 + 100.8+ -50",
                expected: Object::Float(0 as f64),
            },
            VMTestCase {
                input: "(5 + 10 * 2 + 15 / 3) * 2.8 + -10",
                expected: Object::Float(74 as f64),
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
                expected: Object::String(Rc::new(RefCell::new("monkey".to_string()))),
            },
            VMTestCase {
                input: "\"mon\" + \"key\"",
                expected: Object::String(Rc::new(RefCell::new("monkey".to_string()))),
            },
            VMTestCase {
                input: "\"mon\" + \"key\" + \"banana\"",
                expected: Object::String(Rc::new(RefCell::new("monkeybanana".to_string()))),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_array_literals() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "[]",
                expected: Object::Array(Rc::new(RefCell::new(vec![]))),
            },
            VMTestCase {
                input: "[1, 2, 3]",
                expected: Object::Array(Rc::new(RefCell::new(vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                ]))),
            },
            VMTestCase {
                input: "[1 + 2, 3 * 4, 5 + 6]",
                expected: Object::Array(Rc::new(RefCell::new(vec![
                    Object::Integer(3),
                    Object::Integer(12),
                    Object::Integer(11),
                ]))),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_hash_literals() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "{}",
                expected: Object::Hash(Rc::new(RefCell::new(HashMap::<HashKey, Object>::new()))),
            },
            VMTestCase {
                input: "{1: 2, 2: 3}",
                expected: Object::Hash(Rc::new(RefCell::new(HashMap::from([
                    (HashKey::Integer(1), Object::Integer(2)),
                    (HashKey::Integer(2), Object::Integer(3)),
                ])))),
            },
            VMTestCase {
                input: "{1 + 1: 2 * 2, 3 + 3: 4 * 4}",
                expected: Object::Hash(Rc::new(RefCell::new(HashMap::from([
                    (HashKey::Integer(2), Object::Integer(4)),
                    (HashKey::Integer(6), Object::Integer(16)),
                ])))),
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
            VMTestCase {
                input: "\"hello\"[1]",
                expected: Object::Char('e'),
            },
            VMTestCase {
                input: "\"world\"[3]",
                expected: Object::Char('l'),
            },
            VMTestCase {
                input: "\"something\"[999]",
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
    fn test_calling_functions_with_arguments_and_bindings() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "let identity = fn(a) { a; };
                        identity(4);",
                expected: Object::Integer(4),
            },
            VMTestCase {
                input: "let sum = fn(a, b) { a + b; };
                        sum(1, 2);",
                expected: Object::Integer(3),
            },
            VMTestCase {
                input: "let sum = fn(a, b) {
                            let c = a + b;
                            c;
                        };
                        sum(1, 2);",
                expected: Object::Integer(3),
            },
            VMTestCase {
                input: "let sum = fn(a, b) {
                        let c = a + b;
                        c;
                        };
                        sum(1, 2) + sum(3, 4);",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "let sum = fn(a, b) {
                        let c = a + b;
                        c;
                        };
                        let outer = fn() {
                        sum(1, 2) + sum(3, 4);
                        };
                        outer();",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "let globalNum = 10;
                        let sum = fn(a, b) {
                        let c = a + b;
                        c + globalNum;
                        };
                        let outer = fn() {
                        sum(1, 2) + sum(3, 4) + globalNum;
                        };
                        outer() + globalNum;",
                expected: Object::Integer(50),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_calling_functions_with_wrong_arguments() {
        let tests = vec![
            (
                "fn() { 1; }(1);",
                RuntimeError::ArityMismatch {
                    expected: 0,
                    got: 1,
                },
            ),
            (
                "fn(a) { a; }();",
                RuntimeError::ArityMismatch {
                    expected: 1,
                    got: 0,
                },
            ),
            (
                "fn(a, b) { a + b; }(1);",
                RuntimeError::ArityMismatch {
                    expected: 2,
                    got: 1,
                },
            ),
        ];

        for (input, expected) in tests {
            let program = parse_input(input);
            let chars:Vec<char> = input.chars().collect();
            let mut compiler = Compiler::new(&chars);
            compiler
                .compile_program(&program)
                .expect("compilation error");
            let mut vm = VM::new(compiler.bytecode());
            let result = vm.run();
            match result {
                Err(err) => assert_eq!(
                    err, expected,
                    "Got error {:?}, expected {:?}",
                    err, expected
                ),
                Ok(_) => panic!("Expected error {:?}, but got Ok", expected),
            }
        }
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

    #[test]
    fn test_first_class_functions() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "let returnsOne = fn() { 1; };
                        let returnsOneReturner = fn() { returnsOne; };
                        returnsOneReturner()();",
                expected: Object::Integer(1),
            },
            VMTestCase {
                input: "let returnsOneReturner = fn() {
                        let returnsOne = fn() { 1; };
                        returnsOne;
                        };
                        returnsOneReturner()();",
                expected: Object::Integer(1),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_builtin_functions() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "len(\"\")",
                expected: Object::Integer(0),
            },
            VMTestCase {
                input: "len(\"four\")",
                expected: Object::Integer(4),
            },
            VMTestCase {
                input: "len(\"hello world\")",
                expected: Object::Integer(11),
            },
            VMTestCase {
                input: "len([1, 2, 3])",
                expected: Object::Integer(3),
            },
            VMTestCase {
                input: "len([])",
                expected: Object::Integer(0),
            },
            VMTestCase {
                input: "puts(\"hello\", \"world!\")",
                expected: Object::Void,
            },
            VMTestCase {
                input: "first([1, 2, 3])",
                expected: Object::Integer(1),
            },
            VMTestCase {
                input: "first([])",
                expected: Object::Null,
            },
            VMTestCase {
                input: "rest([1, 2, 3])",
                expected: Object::Array(Rc::new(RefCell::new(vec![
                    Object::Integer(2),
                    Object::Integer(3),
                ]))),
            },
            VMTestCase {
                input: "rest([])",
                expected: Object::Null,
            },
            VMTestCase {
                input: "push([], 1)",
                expected: Object::Array(Rc::new(RefCell::new(vec![Object::Integer(1)]))),
            },
            VMTestCase {
                input: "let a = []; push(a, 1); a",
                expected: Object::Array(Rc::new(RefCell::new(vec![]))),
            },
            VMTestCase {
                input: "let a = []; append(a, 1); a",
                expected: Object::Array(Rc::new(RefCell::new(vec![Object::Integer(1)]))),
            },
            VMTestCase {
                input: "let a = [1 ,2]; remove(a, 1); a",
                expected: Object::Array(Rc::new(RefCell::new(vec![Object::Integer(1)]))),
            },
            VMTestCase {
                input: "let a = [1 ,2]; remove(a, 0); a",
                expected: Object::Array(Rc::new(RefCell::new(vec![Object::Integer(2)]))),
            },
            VMTestCase {
                input: "let a = { \"hello\": \"world\", \"one\": \"two\"}; remove(a, \"one\"); a;",
                expected: Object::Hash(Rc::new(RefCell::new(HashMap::from([(
                    HashKey::String("hello".to_string()),
                    Object::String(Rc::new(RefCell::new("world".to_string()))),
                )])))),
            },
            VMTestCase {
                input: "let a = [1 ,2]; pop(a); a",
                expected: Object::Array(Rc::new(RefCell::new(vec![Object::Integer(1)]))),
            },
            VMTestCase {
                input: "let a = [1 ,2]; pop(a);",
                expected: Object::Integer(2),
            },
            VMTestCase {
                input: "let a = [1 ,2]; pop(a); pop(a);",
                expected: Object::Integer(1),
            },
            VMTestCase {
                input: "let a = [1 ,2]; let b = clone(a); pop(a); b",
                expected: Object::Array(Rc::new(RefCell::new(vec![
                    Object::Integer(1),
                    Object::Integer(2),
                ]))),
            },
            VMTestCase {
                input: "let a = [1 ,3]; insert(a, 1, 2); a",
                expected: Object::Array(Rc::new(RefCell::new(vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                ]))),
            },
            VMTestCase {
                input: "let a = { true: 1}; insert(a, false, 2); a",
                expected: Object::Hash(Rc::new(RefCell::new(HashMap::from([
                    (HashKey::Boolean(true), Object::Integer(1)),
                    (HashKey::Boolean(false), Object::Integer(2)),
                ])))),
            },
            VMTestCase {
                input: "let a = { \"hello\": \"world\"}; insert(a, \"one\", \"two\"); a;",
                expected: Object::Hash(Rc::new(RefCell::new(HashMap::from([
                    (
                        HashKey::String("hello".to_string()),
                        Object::String(Rc::new(RefCell::new("world".to_string()))),
                    ),
                    (
                        HashKey::String("one".to_string()),
                        Object::String(Rc::new(RefCell::new("two".to_string()))),
                    ),
                ])))),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_builtin_errors() {
        struct Test {
            input: &'static str,
            expected: RuntimeError,
        }

        let tests = vec![
            Test {
                input: "len(1)",
                expected: RuntimeError::Other("argument to len not supported, got 1".to_string()),
            },
            Test {
                input: "len(\"one\", \"two\")",
                expected: RuntimeError::Other(
                    "wrong number of arguments. got: 2, expected: 1".to_string(),
                ),
            },
            Test {
                input: "first(1)",
                expected: RuntimeError::Other("argument to first not supported, got 1".to_string()),
            },
            Test {
                input: "last(1)",
                expected: RuntimeError::Other("argument to last not supported, got 1".to_string()),
            },
            Test {
                input: "push(1, 1)",
                expected: RuntimeError::Other("argument to push not supported, got 1".to_string()),
            },
        ];

        for test in tests {
            let program = parse_input(test.input);
            let chars: Vec<char> = test.input.chars().collect();
            let mut compiler = Compiler::new(&chars);
            compiler
                .compile_program(&program)
                .expect("compilation error");
            let mut vm = VM::new(compiler.bytecode());
            let result = vm.run();

            match result {
                Err(err) => assert_eq!(
                    test.expected, err,
                    "expected error {:?} got {:?}",
                    test.expected, err
                ),
                Ok(_) => panic!("expected error {:?}, but got Ok", test.expected),
            }
        }
    }

    #[test]
    fn test_closures() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "let newClosure = fn(a) {
                            fn() { a; };
                        };
                        let closure = newClosure(99);
                        closure();",
                expected: Object::Integer(99),
            },
            VMTestCase {
                input: "let newAdder = fn(a, b) {
                            fn(c) { a + b + c };
                        };
                        let adder = newAdder(1, 2);
                        adder(8);",
                expected: Object::Integer(11),
            },
            VMTestCase {
                input: "let newAdder = fn(a, b) {
                            let c = a + b;
                            fn(d) { c + d };
                        };
                        let adder = newAdder(1, 2);
                        adder(8);",
                expected: Object::Integer(11),
            },
            VMTestCase {
                input: "let newAdderOuter = fn(a, b) {
                            let c = a + b;
                            fn(d) {
                                let e = d + c;
                                fn(f) { e + f; };
                            };
                        };
                        let newAdderInner = newAdderOuter(1, 2)
                        let adder = newAdderInner(3);
                        adder(8);",
                expected: Object::Integer(14),
            },
            VMTestCase {
                input: "let a = 1;
                        let newAdderOuter = fn(b) {
                            fn(c) {
                                fn(d) { a + b + c + d };
                            };
                        };
                        let newAdderInner = newAdderOuter(2)
                        let adder = newAdderInner(3);
                        adder(8);",
                expected: Object::Integer(14),
            },
            VMTestCase {
                input: "let newClosure = fn(a, b) {
                            let one = fn() { a; };
                            let two = fn() { b; };
                            fn() { one() + two(); };
                        };
                        let closure = newClosure(9, 90);
                        closure();",
                expected: Object::Integer(99),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_recursive_closures() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "let countDown = fn(x) {
                            if (x == 0) {
                                return 0;
                            } else {
                                countDown(x - 1);
                            }
                        };
                        countDown(1);",
                expected: Object::Integer(0),
            },
            VMTestCase {
                input: "let countDown = fn(x) {
                        if (x == 0) {
                            return 0;
                        } else {
                            countDown(x - 1);
                            }
                        };
                        let wrapper = fn() {
                            countDown(1);
                        };
                        wrapper();",
                expected: Object::Integer(0),
            },
            VMTestCase {
                input: "let wrapper = fn() {
                            let countDown = fn(x) {
                                if (x == 0) {
                                    return 0;
                                } else {
                                countDown(x - 1);
                                }
                            };
                            countDown(1);
                        };
                        wrapper();",
                expected: Object::Integer(0),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_recursive_fibonacci() -> Result<(), RuntimeError> {
        let tests = vec![VMTestCase {
            input: "let fibonacci = fn(x) {
                            if (x == 0) {
                                return 0;
                            } else {
                                if (x == 1) {
                                    return 1;
                                } else {
                                    fibonacci(x - 1) + fibonacci(x - 2);
                                }
                            }
                        };
                        fibonacci(15);",
            expected: Object::Integer(610),
        }];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_assignment() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "let a = 2; a = 1; a",
                expected: Object::Integer(1),
            },
            VMTestCase {
                input: "let a = 2; let b = 2; a = 1; b = 1; a + b",
                expected: Object::Integer(2),
            },
            VMTestCase {
                input: "let a = 1; a = a + 2; a = a + 3; a",
                expected: Object::Integer(6),
            },
            VMTestCase {
                input: "let a = \"hello\"; a = a + \" world\"; a",
                expected: Object::String(Rc::new(RefCell::new("hello world".to_string()))),
            },
            VMTestCase {
                input: "let c = fn() {let a = 2; let b = 2; a = 1; b = 1; a + b}; c()",
                expected: Object::Integer(2),
            },
            VMTestCase {
                input: "let a = [2, 1]; a[0] = 1; a[0]",
                expected: Object::Integer(1),
            },
            VMTestCase {
                input: "let a = { false: 2 }; a[false] = 1; a[false]",
                expected: Object::Integer(1),
            },
            VMTestCase {
                input: "let c = fn() { let h = {true: 10}; h[true] = 99; h[true] }; c()",
                expected: Object::Integer(99),
            },
            VMTestCase {
                input: "let a = 10; let f = fn() { let b = 20; a = 5; b = 1; a + b }; f()",
                expected: Object::Integer(6),
            },
            VMTestCase {
                input: "let b = fn() { let a = 1; let f = fn() { a = 2; a }; f(); a }; b()",
                expected: Object::Integer(2),
            },
            VMTestCase {
                input: "
                        let f = fn() {
                            let a = 0;

                            let b = fn() {
                                a = 1;
                            };

                            b();
                            a
                        }
                        f();
                        ",
                expected: Object::Integer(1),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_while_statemnts() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "let a = 0; while (a < 10) { a = a + 1}; a",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "let b = fn() {let a = 0; while (a < 10) { a = a + 1}; a}; b()",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "let b = fn() { let a = 0; while (a < 3) { a = a + 2 }; a }; b()",
                expected: Object::Integer(4),
            },
            VMTestCase {
                input: "
                    let sum = 0;
                    let i = 0;
                    while (i < 3) {
                        let j = 0;
                        while (j < 2) {
                            sum = sum + 1;
                            j = j + 1;
                        }
                        i = i + 1;
                    }
                    sum
                ",
                expected: Object::Integer(6),
            },
            VMTestCase {
                input: "
                    let nested = fn() {
                        let count = 0;
                        let outer = 0;
                        while (outer < 2) {
                            let inner = 0;
                            while (inner < 3) {
                                count = count + 1;
                                inner = inner + 1;
                            }
                            outer = outer + 1;
                        }
                        count
                    };
                    nested()
                ",
                expected: Object::Integer(6),
            },
            VMTestCase {
                input: "
                    let a = 1;
                    let f = fn() {
                        let b = 2;
                        let g = fn() {
                            let c = 0;
                            while (c < 3) {
                                a = a + 1;
                                b = b + 1;
                                c = c + 1;
                            }
                        };
                        g();
                        a + b
                    };
                    f()
                ",
                expected: Object::Integer(9),
            },
            VMTestCase {
                input: "let a = 0; while (true) { a = a + 1; if (a == 5) {break}}",
                expected: Object::Integer(5),
            },
            VMTestCase {
                input: "let a = 0; let b = 0; while (b < 10) {b = b + 1; if (a == 2) {a = a + 10; continue;}; a = a + 1; }",
                expected: Object::Integer(19),
            },
            VMTestCase {
                input: "let a = 0; let b = 0; while (a < 10) { b = 0; while (b < 9999) { b = b + 1; if (b == 10) {break;} }; a = a + 1 } b",
                expected: Object::Integer(10),
            },
            VMTestCase {
                input: "let a = 0; let b = 0; while (a < 5) { while (b < 9999) { b = b + 1; }; if (a == 2) {break}; a = a + 1; } a",
                expected: Object::Integer(2),
            },
            VMTestCase {
                input: "let f = fn(amount) { let a = 0; while (true) { a = a + 1; if (a == amount) {break;}; }; a }; f(14)",
                expected: Object::Integer(14),
            },
            VMTestCase {
                input: "let count = 0;
                        let sum = 0;

                        while (true) {
                            count = count + 1;
                            
                            if (count / 2 * 2 != count) {
                                continue;
                            }
                            
                            if (count > 15) {
                                break;
                            }
                            
                            sum = sum + count;
                        }

                        sum",
                expected: Object::Integer(56),
            },
        ];

        run_vm_tests(&tests)
    }

    #[test]
    fn test_char_literals() -> Result<(), RuntimeError> {
        let tests = vec![
            VMTestCase {
                input: "'5'",
                expected: Object::Char('5'),
            },
            VMTestCase {
                input: "'a'",
                expected: Object::Char('a'),
            },
            VMTestCase {
                input: "'B'",
                expected: Object::Char('B'),
            },
            VMTestCase {
                input: "'W'",
                expected: Object::Char('W'),
            },
        ];

        run_vm_tests(&tests)
    }
}
