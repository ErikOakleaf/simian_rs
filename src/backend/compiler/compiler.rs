use std::cell::RefCell;
use std::rc::Rc;

use crate::backend::{OPERAND_WIDTHS, Opcode, Symbol, SymbolScope, SymbolTable, make};
use crate::frontend::ast::{BlockStatement, Expression, Program, Statement};
use crate::runtime::builtins::BUILTINS;
use crate::runtime::object::{CompiledFunction, Object};

#[derive(Debug)]
#[allow(dead_code)]
pub enum CompilationError {
    UnknownOperator(String),
    UnknownSymbol(String),
    Unassignable(Expression),
    DefiningAlreadyExistingSymbol(String),
}

#[derive(Clone, Copy)]
struct EmittedInstruction {
    opcode: Opcode,
    position: usize,
}

struct CompilationScope {
    instructions: Vec<u8>,
    last_instruction: EmittedInstruction,
    previous_instruction: EmittedInstruction,
}

impl CompilationScope {
    fn new() -> Self {
        CompilationScope {
            instructions: Vec::<u8>::new(),
            last_instruction: EmittedInstruction {
                opcode: Opcode::LoadConstant,
                position: 0,
            },
            previous_instruction: EmittedInstruction {
                opcode: Opcode::LoadConstant,
                position: 0,
            },
        }
    }
}

pub struct Compiler {
    pub constants: Vec<Object>,
    pub symbol_table: Rc<RefCell<SymbolTable>>,

    scopes: Vec<CompilationScope>,
    scope_index: usize,
}

impl Compiler {
    pub fn new() -> Self {
        let symbol_table = SymbolTable::new();
        for (i, builtin) in BUILTINS.iter().enumerate() {
            symbol_table
                .borrow_mut()
                .define_builtin(i as u16, builtin.name);
        }

        Compiler {
            constants: Vec::<Object>::new(),
            symbol_table: symbol_table,
            scopes: vec![CompilationScope::new()],
            scope_index: 0,
        }
    }

    pub fn new_with_state(symbol_table: Rc<RefCell<SymbolTable>>, constants: Vec<Object>) -> Self {
        let mut compiler = Compiler::new();
        compiler.symbol_table = symbol_table;
        compiler.constants = constants;
        compiler
    }

    fn add_constant(&mut self, object: Object) -> u16 {
        self.constants.push(object);
        (self.constants.len() - 1) as u16
    }

    fn add_instruction(&mut self, opcode: Opcode, operands: &[&[u8]]) -> usize {
        let current_instructions = self.current_intstructions();
        let position = current_instructions.len();
        make(current_instructions, opcode, operands);
        position
    }

    pub fn compile_program(&mut self, program: &Program) -> Result<(), CompilationError> {
        for statement in program.statements.iter() {
            self.compile_statement(statement)?;
        }

        Ok(())
    }

    fn compile_statement(&mut self, statement: &Statement) -> Result<(), CompilationError> {
        match statement {
            Statement::Expression(expression_statement) => {
                self.compile_expression(expression_statement.expression.as_ref())?;
                self.emit(Opcode::Pop, &[]);
            }
            Statement::Let(let_statement) => {
                let name = &let_statement.name.token.literal;

                if let Some(existing) = self.symbol_table.borrow().store.get(name) {
                    if existing.scope != SymbolScope::Function {
                        return Err(CompilationError::DefiningAlreadyExistingSymbol(
                            name.to_string(),
                        ));
                    }
                }

                let symbol = self
                    .symbol_table
                    .borrow_mut()
                    .define(&let_statement.name.token.literal);

                self.compile_expression(let_statement.value.as_ref())?;

                if symbol.scope == SymbolScope::Global {
                    let index = symbol.index.to_be_bytes();
                    self.emit(Opcode::SetGlobal, &[&index]);
                } else {
                    let index = [symbol.index as u8];
                    self.emit(Opcode::SetLocal, &[&index]);
                }
            }
            Statement::Return(return_statement) => {
                self.compile_expression(return_statement.return_value.as_ref())?;
                self.emit(Opcode::ReturnValue, &[]);
            }
            Statement::Assign(assign_statement) => match assign_statement.target.as_ref() {
                Expression::Identifier(identifier_expression) => {
                    self.compile_expression(assign_statement.value.as_ref())?;

                    let symbol = self
                        .symbol_table
                        .borrow_mut()
                        .resolve(&identifier_expression.token.literal)?;

                    match symbol.scope {
                        SymbolScope::Global => {
                            let index = symbol.index.to_be_bytes();
                            self.emit(Opcode::SetGlobal, &[&index]);
                        }
                        SymbolScope::Local => {
                            let index = symbol.index as u8;
                            self.emit(Opcode::SetLocal, &[&[index]]);
                        }
                        SymbolScope::Free => {
                            let index = symbol.index as u8;
                            self.emit(Opcode::AssignFree, &[&[index]]);
                        }
                        _ => unreachable!("unasignable scope"),
                    };
                }
                Expression::Index(index_expression) => {
                    self.compile_expression(index_expression.left.as_ref())?;
                    self.compile_expression(index_expression.index.as_ref())?;
                    self.compile_expression(assign_statement.value.as_ref())?;
                    self.emit(Opcode::AssignIndexable, &[]);
                }
                _ => {
                    return Err(CompilationError::Unassignable(
                        *assign_statement.target.clone(),
                    ));
                }
            },
            Statement::While(while_statement) => {
                let start_bytes = ((self.current_intstructions().len()) as u16).to_be_bytes();

                self.compile_expression(while_statement.condition.as_ref())?;

                let jump_not_truthy_position = self.emit(Opcode::JumpNotTruthy, &[&[0, 0]]);

                self.compile_block_statement(&while_statement.body)?;
                self.emit(Opcode::Jump, &[&start_bytes]);

                let current_position_bytes =
                    ((self.current_intstructions().len()) as u16).to_be_bytes();

                self.change_operands(jump_not_truthy_position, &[&current_position_bytes])?;
            }
        };
        Ok(())
    }

    fn compile_expression(&mut self, expression: &Expression) -> Result<(), CompilationError> {
        match expression {
            Expression::IntegerLiteral(integer_literal_expression) => {
                let integer = Object::Integer(integer_literal_expression.value);
                let position = self.add_constant(integer);
                self.emit(Opcode::LoadConstant, &[&position.to_be_bytes()]);
            }
            Expression::FloatLiteral(float_value) => {
                let float = Object::Float(*float_value);
                let position = self.add_constant(float);
                self.emit(Opcode::LoadConstant, &[&position.to_be_bytes()]);
            }
            Expression::Boolean(boolean_literal_expression) => {
                let bool_value = boolean_literal_expression.value;
                let bool_opcode = match bool_value {
                    true => Opcode::True,
                    false => Opcode::False,
                };
                self.emit(bool_opcode, &[]);
            }
            Expression::Identifier(identifier_expression) => {
                let symbol = self
                    .symbol_table
                    .borrow_mut()
                    .resolve(&identifier_expression.token.literal)?;

                self.load_symbol(symbol);
            }
            Expression::String(string_token) => {
                let string_object =
                    Object::String(Rc::new(RefCell::new(string_token.literal.clone())));
                let index = self.add_constant(string_object).to_be_bytes();
                self.emit(Opcode::LoadConstant, &[&index]);
            }
            Expression::Array(array_literal_expression) => {
                for element in array_literal_expression.elements.iter() {
                    self.compile_expression(element)?;
                }

                let length = array_literal_expression.elements.len() as u16;
                let length_bytes = length.to_be_bytes();
                self.emit(Opcode::Array, &[&length_bytes]);
            }
            Expression::Hash(hash_literal_expression) => {
                for pair in hash_literal_expression.pairs.iter() {
                    // key
                    self.compile_expression(&pair.0)?;
                    // value
                    self.compile_expression(&pair.1)?;
                }

                let length = (hash_literal_expression.pairs.len() * 2) as u16;
                let length_bytes = length.to_be_bytes();
                self.emit(Opcode::Hash, &[&length_bytes]);
            }
            Expression::Function(function_literal_expression) => {
                self.enter_scope();

                if let Some(ref name) = function_literal_expression.name {
                    self.symbol_table.borrow_mut().define_function_name(name);
                }

                for parameter in function_literal_expression.parameters.iter() {
                    self.symbol_table
                        .borrow_mut()
                        .define(&parameter.token.literal);
                }

                self.compile_block_statement(&function_literal_expression.body)?;

                if self.last_instruction_is(Opcode::Pop) {
                    self.replace_last_pop_with_return();
                }
                if !self.last_instruction_is(Opcode::ReturnValue) {
                    self.emit(Opcode::Return, &[]);
                }

                let free_symbols = self.symbol_table.borrow().free_symbols.clone();
                let free_symbols_amount = free_symbols.len() as u8;
                let amount_locals = self.symbol_table.borrow().amount_definitions;
                let instructions = self.leave_scope();

                let compiled_function = Object::CompiledFunction(Rc::new(CompiledFunction::new(
                    instructions,
                    amount_locals,
                    function_literal_expression.parameters.len(),
                )));

                let function_index = self.add_constant(compiled_function);

                let mut local_indices = Vec::<u8>::new();
                for symbol in free_symbols {
                    match symbol.scope {
                        SymbolScope::Local => {
                            local_indices.push(0); // Local
                            local_indices.push(symbol.index as u8);
                        }
                        SymbolScope::Free => {
                            local_indices.push(1); // Free
                            local_indices.push(symbol.index as u8);
                        }
                        _ => unreachable!("free symbol has unexpected scope: {:?}", symbol.scope),
                    }
                }
                self.emit(
                    Opcode::Closure,
                    &[
                        &function_index.to_be_bytes(),
                        &[free_symbols_amount],
                        &local_indices,
                    ],
                );
            }
            Expression::Call(call_expression) => {
                self.compile_expression(call_expression.function.as_ref())?;
                for argument in call_expression.arguments.iter() {
                    self.compile_expression(argument)?;
                }
                self.emit(Opcode::Call, &[&[call_expression.arguments.len() as u8]]);
            }
            Expression::Infix(infix_expression) => {
                let operator = infix_expression.token.literal.as_str();

                if operator == "<" {
                    self.compile_expression(&infix_expression.right)?;
                    self.compile_expression(&infix_expression.left)?;
                    self.emit(Opcode::GreaterThan, &[]);
                    return Ok(());
                }

                self.compile_expression(infix_expression.left.as_ref())?;
                self.compile_expression(infix_expression.right.as_ref())?;

                match operator {
                    "+" => self.emit(Opcode::Add, &[]),
                    "-" => self.emit(Opcode::Sub, &[]),
                    "*" => self.emit(Opcode::Mul, &[]),
                    "/" => self.emit(Opcode::Div, &[]),
                    ">" => self.emit(Opcode::GreaterThan, &[]),
                    "==" => self.emit(Opcode::Equal, &[]),
                    "!=" => self.emit(Opcode::NotEqual, &[]),
                    _ => return Err(CompilationError::UnknownOperator(operator.to_string())),
                };
            }
            Expression::Prefix(prefix_expression) => {
                let operator = prefix_expression.token.literal.as_str();

                self.compile_expression(prefix_expression.right.as_ref())?;

                match operator {
                    "-" => self.emit(Opcode::Minus, &[]),
                    "!" => self.emit(Opcode::Bang, &[]),
                    _ => return Err(CompilationError::UnknownOperator(operator.to_string())),
                };
            }
            Expression::If(if_expression) => {
                self.compile_expression(if_expression.condition.as_ref())?;

                let jump_not_truthy_position = self.emit(Opcode::JumpNotTruthy, &[&[0xFF, 0xFF]]);

                self.compile_block_statement(&if_expression.consequence)?;

                if self.last_instruction_is(Opcode::Pop) {
                    self.remove_last_pop();
                }

                let jump_position = self.emit(Opcode::Jump, &[&[0xFF, 0xFF]]);
                let after_consequence_position = self.get_current_position();
                self.change_operands(jump_not_truthy_position, &[&after_consequence_position])?;

                match &if_expression.alternative {
                    None => {
                        self.emit(Opcode::Null, &[]);
                    }
                    Some(alternative) => {
                        self.compile_block_statement(alternative)?;

                        if self.last_instruction_is(Opcode::Pop) {
                            self.remove_last_pop();
                        }
                    }
                };

                let after_alternative_position = self.get_current_position();
                self.change_operands(jump_position, &[&after_alternative_position])?;
            }
            Expression::Index(index_expression) => {
                self.compile_expression(index_expression.left.as_ref())?;
                self.compile_expression(index_expression.index.as_ref())?;
                self.emit(Opcode::Index, &[]);
            }
        };

        Ok(())
    }

    fn compile_block_statement(
        &mut self,
        block_statement: &BlockStatement,
    ) -> Result<(), CompilationError> {
        for statement in block_statement.statements.iter() {
            self.compile_statement(statement)?;
        }
        Ok(())
    }

    fn emit(&mut self, opcode: Opcode, operands: &[&[u8]]) -> usize {
        let position = self.add_instruction(opcode, operands);

        self.set_last_instruction(opcode, position);

        position
    }

    fn enter_scope(&mut self) {
        let scope = CompilationScope::new();
        self.scopes.push(scope);
        self.scope_index += 1;

        let new_table = SymbolTable::new_enclosed(Rc::clone(&self.symbol_table));
        self.symbol_table = new_table;
    }

    fn leave_scope(&mut self) -> Box<[u8]> {
        let instructions = self.scopes[self.scope_index]
            .instructions
            .clone()
            .into_boxed_slice();

        self.scopes.truncate(self.scopes.len() - 1);
        self.scope_index -= 1;

        let outer = self
            .symbol_table
            .borrow()
            .outer
            .as_ref()
            .expect("No outer scope to return to!")
            .clone();

        self.symbol_table = outer;

        instructions
    }

    pub fn bytecode(&self) -> Bytecode {
        Bytecode {
            instructions: self.scopes[self.scope_index]
                .instructions
                .clone()
                .into_boxed_slice(),
            constants: self.constants.clone().into_boxed_slice(),
        }
    }

    // Helpers

    #[inline]
    fn set_last_instruction(&mut self, opcode: Opcode, position: usize) {
        let scope = &mut self.scopes[self.scope_index];

        scope.previous_instruction = scope.last_instruction;
        scope.last_instruction = EmittedInstruction {
            opcode: opcode,
            position: position,
        }
    }

    #[inline]
    fn change_operands(
        &mut self,
        opcode_position: usize,
        new_operands: &[&[u8]],
    ) -> Result<(), CompilationError> {
        let current_instructions = self.current_intstructions();
        let opcode = Opcode::from_byte(current_instructions[opcode_position]);

        let expected_operands_amount = OPERAND_WIDTHS[opcode as usize].amount;
        debug_assert_eq!(
            expected_operands_amount,
            new_operands.len(),
            "amount of operands for opcode {} is not correct expected {} got {}",
            opcode,
            expected_operands_amount,
            new_operands.len(),
        );

        for (i, expected_width) in OPERAND_WIDTHS[opcode as usize].widths.iter().enumerate() {
            let width = new_operands[i].len();

            if width == usize::MAX {
                continue;
            }

            debug_assert_eq!(
                *expected_width, width,
                "operand {} for opcode {} does not have the correct width expected {} got {}",
                i, opcode, expected_width, width
            );
        }

        let total_operands_length: usize = new_operands.iter().map(|op| op.len()).sum();
        let mut flattened = Vec::with_capacity(total_operands_length);
        for operand in new_operands {
            flattened.extend_from_slice(operand);
        }

        let operand_start = opcode_position + 1;
        let operand_end = operand_start + total_operands_length;

        current_instructions[operand_start..operand_end].copy_from_slice(&flattened);

        Ok(())
    }

    #[inline]
    fn load_symbol(&mut self, symbol: Symbol) {
        match symbol.scope {
            SymbolScope::Global => self.emit(Opcode::GetGlobal, &[&symbol.index.to_be_bytes()]),
            SymbolScope::Local => self.emit(Opcode::GetLocal, &[&[symbol.index as u8]]),
            SymbolScope::Builtin => self.emit(Opcode::GetBuiltin, &[&[symbol.index as u8]]),
            SymbolScope::Free => self.emit(Opcode::GetFree, &[&[symbol.index as u8]]),
            SymbolScope::Function => self.emit(Opcode::CurrentClosure, &[]),
        };
    }

    fn replace_last_pop_with_return(&mut self) {
        let last_position = self.scopes[self.scope_index].last_instruction.position;
        let current_instructions = self.current_intstructions();
        current_instructions[last_position] = Opcode::ReturnValue as u8;
        self.scopes[self.scope_index].last_instruction.opcode = Opcode::ReturnValue;
    }

    #[inline(always)]
    fn remove_last_pop(&mut self) {
        let scope = &mut self.scopes[self.scope_index];

        let last_pos = scope.last_instruction.position;
        scope.instructions.truncate(last_pos);

        scope.last_instruction = scope.previous_instruction;
    }

    #[inline(always)]
    fn get_current_position(&self) -> [u8; 2] {
        let after_consequence_position = self.scopes[self.scope_index].instructions.len() as u16;
        after_consequence_position.to_be_bytes()
    }

    #[inline(always)]
    fn current_intstructions(&mut self) -> &mut Vec<u8> {
        &mut self.scopes[self.scope_index].instructions
    }

    #[inline(always)]
    fn last_instruction_is(&self, opcode: Opcode) -> bool {
        self.scopes[self.scope_index].last_instruction.opcode == opcode
    }
}

pub struct Bytecode {
    pub instructions: Box<[u8]>,
    pub constants: Box<[Object]>,
}

// Helpers

#[allow(dead_code)]
fn format_instructions(instructions: &[u8]) -> String {
    let mut result = String::new();

    let mut i = 0;
    while i < instructions.len() {
        let address = i;
        let opcode = Opcode::from_byte(instructions[i]);
        i += 1;

        let (operands, offset) = read_operand(opcode.clone(), &instructions[i..]);
        i += offset;

        let operands_str = operands
            .iter()
            .map(|val| val.to_string())
            .collect::<Vec<_>>()
            .join(" ");

        let instruction_string = if operands_str.is_empty() {
            format!("{:04} {}\n", address, opcode)
        } else {
            format!("{:04} {} {}\n", address, opcode, operands_str)
        };

        result.push_str(&instruction_string);
    }

    result
}

fn read_operand(opcode: Opcode, instructions: &[u8]) -> (Box<[usize]>, usize) {
    let operands_amount = OPERAND_WIDTHS[opcode as usize].amount;
    let operand_widths = OPERAND_WIDTHS[opcode as usize].widths;

    let mut operands = Vec::<usize>::new();
    let mut offset = 0;

    for i in 0..operands_amount {
        let width = operand_widths[i];

        if width == 0 {
            continue;
        }

        if width == usize::MAX {
            for &byte in &instructions[offset..] {
                operands.push(byte as usize);
            }
            offset = instructions.len();
            break;
        }

        let value: usize = match width {
            1 => instructions[offset] as usize,
            2 => u16::from_be_bytes([instructions[offset], instructions[offset + 1]]) as usize,
            _ => panic!("unsupported operand width"),
        };

        operands.push(value);
        offset += width;
    }

    (operands.into_boxed_slice(), offset)
}

#[cfg(test)]
mod tests {
    use crate::{frontend::ast::Program, frontend::lexer::Lexer, frontend::parser::Parser};

    use super::*;

    #[derive(Debug)]
    struct CompilerTestCase {
        input: &'static str,
        expected_constants: Vec<Object>,
        expected_instructions: Vec<u8>,
    }

    struct FormattingTestCase {
        instructions: Vec<u8>,
        expected: &'static str,
    }

    // Test helpers

    fn parse_input(input: &str) -> Program {
        let mut lexer = Lexer::new(input);
        let mut parser = Parser::new(&mut lexer);
        parser.parse_program().unwrap()
    }

    fn run_compiler_tests(tests: Vec<CompilerTestCase>) {
        for test in tests {
            let program = parse_input(test.input);
            let mut compiler = Compiler::new();
            compiler.compile_program(&program).unwrap();

            let bytecode = compiler.bytecode();

            // flatten expected instructions
            assert_eq!(
                &test.expected_constants,
                bytecode.constants.as_ref(),
                "test failed for input: {}\nexpected constants:\n{:?} got:\n{:?}",
                test.input,
                &test.expected_constants,
                bytecode.constants.as_ref(),
            );

            assert_eq!(
                &test.expected_instructions,
                bytecode.instructions.as_ref(),
                "test failed for input: {}\nexpected instructions:\n{}got:\n{}",
                test.input,
                format_instructions(&test.expected_instructions),
                format_instructions(bytecode.instructions.as_ref()),
            );
        }
    }

    fn make_instructions(instructions: Vec<(Opcode, &[&[u8]])>) -> Vec<u8> {
        let mut result = Vec::<u8>::new();
        for (instruction, opcode) in instructions {
            make(&mut result, instruction, opcode);
        }
        result
    }

    // Tests

    #[test]
    fn test_integer_arithmetic() {
        let tests = vec![
            CompilerTestCase {
                input: "1 + 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&vec![0, 0]]),
                    (Opcode::LoadConstant, &[&vec![0, 1]]),
                    (Opcode::Add, &vec![]),
                    (Opcode::Pop, &vec![]),
                ]),
            },
            CompilerTestCase {
                input: "1; 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&vec![0, 0]]),
                    (Opcode::Pop, &vec![]),
                    (Opcode::LoadConstant, &[&vec![0, 1]]),
                    (Opcode::Pop, &vec![]),
                ]),
            },
            CompilerTestCase {
                input: "1 - 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&vec![0, 0]]),
                    (Opcode::LoadConstant, &[&vec![0, 1]]),
                    (Opcode::Sub, &vec![]),
                    (Opcode::Pop, &vec![]),
                ]),
            },
            CompilerTestCase {
                input: "1 * 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&vec![0, 0]]),
                    (Opcode::LoadConstant, &[&vec![0, 1]]),
                    (Opcode::Mul, &vec![]),
                    (Opcode::Pop, &vec![]),
                ]),
            },
            CompilerTestCase {
                input: "2 / 1",
                expected_constants: vec![Object::Integer(2), Object::Integer(1)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&vec![0, 0]]),
                    (Opcode::LoadConstant, &[&vec![0, 1]]),
                    (Opcode::Div, &vec![]),
                    (Opcode::Pop, &vec![]),
                ]),
            },
            CompilerTestCase {
                input: "-1",
                expected_constants: vec![Object::Integer(1)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&vec![0, 0]]),
                    (Opcode::Minus, &vec![]),
                    (Opcode::Pop, &vec![]),
                ]),
            },
            CompilerTestCase {
                input: "!true",
                expected_constants: vec![],
                expected_instructions: make_instructions(vec![
                    (Opcode::True, &vec![]),
                    (Opcode::Bang, &vec![]),
                    (Opcode::Pop, &vec![]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_boolean_expressions() {
        let tests = vec![
            CompilerTestCase {
                input: "true",
                expected_constants: vec![],
                expected_instructions: make_instructions(vec![
                    (Opcode::True, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "false",
                expected_constants: vec![],
                expected_instructions: make_instructions(vec![
                    (Opcode::False, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "1 > 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0x00, 0x00]]),
                    (Opcode::LoadConstant, &[&[0x00, 0x01]]),
                    (Opcode::GreaterThan, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "1 < 2",
                expected_constants: vec![Object::Integer(2), Object::Integer(1)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0x00, 0x00]]),
                    (Opcode::LoadConstant, &[&[0x00, 0x01]]),
                    (Opcode::GreaterThan, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "1 == 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0x00, 0x00]]),
                    (Opcode::LoadConstant, &[&[0x00, 0x01]]),
                    (Opcode::Equal, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "1 != 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0x00, 0x00]]),
                    (Opcode::LoadConstant, &[&[0x00, 0x01]]),
                    (Opcode::NotEqual, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "true == false",
                expected_constants: vec![],
                expected_instructions: make_instructions(vec![
                    (Opcode::True, &[]),
                    (Opcode::False, &[]),
                    (Opcode::Equal, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "true != false",
                expected_constants: vec![],
                expected_instructions: make_instructions(vec![
                    (Opcode::True, &[]),
                    (Opcode::False, &[]),
                    (Opcode::NotEqual, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_conditionals() {
        let tests = vec![
            CompilerTestCase {
                input: "if (true) { 10 }; 3333",
                expected_constants: vec![Object::Integer(10), Object::Integer(3333)],
                expected_instructions: make_instructions(vec![
                    (Opcode::True, &[]),
                    (Opcode::JumpNotTruthy, &[&[0x00, 10]]),
                    (Opcode::LoadConstant, &[&[0x00, 0x00]]),
                    (Opcode::Jump, &[&[0, 11]]),
                    (Opcode::Null, &[]),
                    (Opcode::Pop, &[]),
                    (Opcode::LoadConstant, &[&[0x00, 0x01]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "if (true) { 10 } else { 20 }; 3333",
                expected_constants: vec![
                    Object::Integer(10),
                    Object::Integer(20),
                    Object::Integer(3333),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::True, &[]),
                    (Opcode::JumpNotTruthy, &[&[0x00, 10]]),
                    (Opcode::LoadConstant, &[&[0x00, 0x00]]),
                    (Opcode::Jump, &[&[0x00, 13]]),
                    (Opcode::LoadConstant, &[&[0x00, 0x01]]),
                    (Opcode::Pop, &[]),
                    (Opcode::LoadConstant, &[&[0x00, 0x02]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_global_let_statements() {
        let tests = vec![
            CompilerTestCase {
                input: "let one = 1; let two = 2;",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::SetGlobal, &[&[0, 1]]),
                ]),
            },
            CompilerTestCase {
                input: "let one = 1; one;",
                expected_constants: vec![Object::Integer(1)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::GetGlobal, &[&[0, 0]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "let one = 1; let two = one; two;",
                expected_constants: vec![Object::Integer(1)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::GetGlobal, &[&[0, 0]]),
                    (Opcode::SetGlobal, &[&[0, 1]]),
                    (Opcode::GetGlobal, &[&[0, 1]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_string_expression() {
        let tests = vec![
            CompilerTestCase {
                input: "\"monkey\"",
                expected_constants: vec![Object::String(Rc::new(RefCell::new(
                    "monkey".to_string(),
                )))],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "\"mon\" + \"key\"",
                expected_constants: vec![
                    Object::String(Rc::new(RefCell::new("mon".to_string()))),
                    Object::String(Rc::new(RefCell::new("key".to_string()))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::Add, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_array_literals() {
        let tests = vec![
            CompilerTestCase {
                input: "[]",
                expected_constants: vec![],
                expected_instructions: make_instructions(vec![
                    (Opcode::Array, &[&[0, 0]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "[1, 2, 3]",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::Array, &[&[0, 3]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "[1 + 2, 3 - 4, 5 * 6]",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                    Object::Integer(4),
                    Object::Integer(5),
                    Object::Integer(6),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::Add, &[]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::LoadConstant, &[&[0, 3]]),
                    (Opcode::Sub, &[]),
                    (Opcode::LoadConstant, &[&[0, 4]]),
                    (Opcode::LoadConstant, &[&[0, 5]]),
                    (Opcode::Mul, &[]),
                    (Opcode::Array, &[&[0, 3]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_hash_literals() {
        let tests = vec![
            CompilerTestCase {
                input: "{}",
                expected_constants: vec![],
                expected_instructions: make_instructions(vec![
                    (Opcode::Hash, &[&[0, 0]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "{1: 2, 3: 4, 5: 6}",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                    Object::Integer(4),
                    Object::Integer(5),
                    Object::Integer(6),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::LoadConstant, &[&[0, 3]]),
                    (Opcode::LoadConstant, &[&[0, 4]]),
                    (Opcode::LoadConstant, &[&[0, 5]]),
                    (Opcode::Hash, &[&[0, 6]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "{1: 2 + 3, 4: 5 * 6}",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                    Object::Integer(4),
                    Object::Integer(5),
                    Object::Integer(6),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::Add, &[]),
                    (Opcode::LoadConstant, &[&[0, 3]]),
                    (Opcode::LoadConstant, &[&[0, 4]]),
                    (Opcode::LoadConstant, &[&[0, 5]]),
                    (Opcode::Mul, &[]),
                    (Opcode::Hash, &[&[0, 4]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_index_expressions() {
        let tests = vec![
            CompilerTestCase {
                input: "[1, 2, 3][1 + 1]",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                    Object::Integer(1),
                    Object::Integer(1),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::Array, &[&[0, 3]]),
                    (Opcode::LoadConstant, &[&[0, 3]]),
                    (Opcode::LoadConstant, &[&[0, 4]]),
                    (Opcode::Add, &[]),
                    (Opcode::Index, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "{1: 2}[2 - 1]",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(2),
                    Object::Integer(1),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::Hash, &[&[0, 2]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::LoadConstant, &[&[0, 3]]),
                    (Opcode::Sub, &[]),
                    (Opcode::Index, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_functions() {
        let tests = vec![
            CompilerTestCase {
                input: "fn() { return 5 + 10 }",
                expected_constants: vec![
                    Object::Integer(5),
                    Object::Integer(10),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::Add, &[]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 2], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "fn() { 5 + 10 }",
                expected_constants: vec![
                    Object::Integer(5),
                    Object::Integer(10),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::Add, &[]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 2], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "fn() { 1; 2 }",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::Pop, &[]),
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 2], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_functions_without_return_value() {
        let tests = vec![CompilerTestCase {
            input: "fn() {}",
            expected_constants: vec![Object::CompiledFunction(Rc::new(CompiledFunction::new(
                make_instructions(vec![(Opcode::Return, &[])]).into_boxed_slice(),
                0,
                0,
            )))],
            expected_instructions: make_instructions(vec![
                (Opcode::Closure, &[&[0, 0], &[0], &[]]),
                (Opcode::Pop, &[]),
            ]),
        }];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_function_calls() {
        let tests = vec![
            CompilerTestCase {
                input: "fn() { 24 }();",
                expected_constants: vec![
                    Object::Integer(24),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 1], &[0], &[]]),
                    (Opcode::Call, &[&[0]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "let noArg = fn() { 24 };
                        noArg();",
                expected_constants: vec![
                    Object::Integer(24),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 1], &[0], &[]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::GetGlobal, &[&[0, 0]]),
                    (Opcode::Call, &[&[0]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "let oneArg = fn(a) { };
                        oneArg(24);",
                expected_constants: vec![
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![(Opcode::Return, &[])]).into_boxed_slice(),
                        1,
                        1,
                    ))),
                    Object::Integer(24),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 0], &[0], &[]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::GetGlobal, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::Call, &[&[1]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "let manyArg = fn(a, b, c) { };
                        manyArg(24, 25, 26);",
                expected_constants: vec![
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![(Opcode::Return, &[])]).into_boxed_slice(),
                        3,
                        3,
                    ))),
                    Object::Integer(24),
                    Object::Integer(25),
                    Object::Integer(26),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 0], &[0], &[]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::GetGlobal, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::LoadConstant, &[&[0, 3]]),
                    (Opcode::Call, &[&[3]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "let oneArg = fn(a) { a };
                        oneArg(24);",
                expected_constants: vec![
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        1,
                    ))),
                    Object::Integer(24),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 0], &[0], &[]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::GetGlobal, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::Call, &[&[1]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "let manyArg = fn(a, b, c) { a; b; c; };
                        manyArg(24, 25, 26);",
                expected_constants: vec![
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::Pop, &[]),
                            (Opcode::GetLocal, &[&[1]]),
                            (Opcode::Pop, &[]),
                            (Opcode::GetLocal, &[&[2]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        3,
                        3,
                    ))),
                    Object::Integer(24),
                    Object::Integer(25),
                    Object::Integer(26),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 0], &[0], &[]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::GetGlobal, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::LoadConstant, &[&[0, 3]]),
                    (Opcode::Call, &[&[3]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_let_statement_scopes() {
        let tests = vec![
            CompilerTestCase {
                input: "let num = 55;
                        fn() { num }",
                expected_constants: vec![
                    Object::Integer(55),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::GetGlobal, &[&[0, 0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::Closure, &[&[0, 1], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "fn() {
                            let num = 55;
                            num
                        }",
                expected_constants: vec![
                    Object::Integer(55),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::SetLocal, &[&[0]]),
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 1], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "fn() {
                                let a = 55;
                                let b = 77;
                                a + b
                        }",
                expected_constants: vec![
                    Object::Integer(55),
                    Object::Integer(77),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::SetLocal, &[&[0]]),
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::SetLocal, &[&[1]]),
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::GetLocal, &[&[1]]),
                            (Opcode::Add, &[]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        2,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 2], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_builtins() {
        let tests = vec![
            CompilerTestCase {
                input: "len([]);
                    push([], 1);",
                expected_constants: vec![Object::Integer(1)],
                expected_instructions: make_instructions(vec![
                    (Opcode::GetBuiltin, &[&[0]]),
                    (Opcode::Array, &[&[0, 0]]),
                    (Opcode::Call, &[&[1]]),
                    (Opcode::Pop, &[]),
                    (Opcode::GetBuiltin, &[&[5]]),
                    (Opcode::Array, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::Call, &[&[2]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "fn() { len([]) }",
                expected_constants: vec![Object::CompiledFunction(Rc::new(CompiledFunction::new(
                    make_instructions(vec![
                        (Opcode::GetBuiltin, &[&[0]]),
                        (Opcode::Array, &[&[0, 0]]),
                        (Opcode::Call, &[&[1]]),
                        (Opcode::ReturnValue, &[]),
                    ])
                    .into_boxed_slice(),
                    0,
                    0,
                )))],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 0], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_closures() {
        let tests = vec![
            CompilerTestCase {
                input: "fn(a) {
                            fn(b) {
                                a + b
                            }
                        }",
                expected_constants: vec![
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::GetFree, &[&[0]]),
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::Add, &[]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        1,
                    ))),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::Closure, &[&[0, 0], &[1], &[0, 0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        1,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 1], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "fn(a) {
                            fn(b) {
                                fn(c) {
                                    a + b + c
                                }
                            }
                        };",
                expected_constants: vec![
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::GetFree, &[&[0]]),
                            (Opcode::GetFree, &[&[1]]),
                            (Opcode::Add, &[]),
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::Add, &[]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        1,
                    ))),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::Closure, &[&[0, 0], &[2], &[1, 0, 0, 0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        1,
                    ))),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::Closure, &[&[0, 1], &[1], &[0 ,0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        1,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 2], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "let global = 55;
                        fn() {
                            let a = 66;
                            fn() {
                                let b = 77;
                                fn() {
                                    let c = 88;
                                    global + a + b + c;
                                }
                            }
                        }",
                expected_constants: vec![
                    Object::Integer(55),
                    Object::Integer(66),
                    Object::Integer(77),
                    Object::Integer(88),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 3]]),
                            (Opcode::SetLocal, &[&[0]]),
                            (Opcode::GetGlobal, &[&[0, 0]]),
                            (Opcode::GetFree, &[&[0]]),
                            (Opcode::Add, &[]),
                            (Opcode::GetFree, &[&[1]]),
                            (Opcode::Add, &[]),
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::Add, &[]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        0,
                    ))),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 2]]),
                            (Opcode::SetLocal, &[&[0]]),
                            // (Opcode::GetFree, &[&[0]]),
                            // (Opcode::GetLocal, &[&[0]]),
                            (Opcode::Closure, &[&[0, 4], &[2], &[1, 0, 0, 0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        0,
                    ))),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::SetLocal, &[&[0]]),
                            // (Opcode::GetLocal, &[&[0]]),
                            (Opcode::Closure, &[&[0, 5], &[1], &[0, 0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::Closure, &[&[0, 6], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_recursive_functions() {
        let tests = vec![
            CompilerTestCase {
                input: "let countDown = fn(x) { countDown(x - 1); };
                        countDown(1);",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::CurrentClosure, &[]),
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::Sub, &[]),
                            (Opcode::Call, &[&[1]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        1,
                    ))),
                    Object::Integer(1),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 1], &[0], &[]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::GetGlobal, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::Call, &[&[1]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "let wrapper = fn() {
                            let countDown = fn(x) { countDown(x - 1); };
                            countDown(1);
                            };
                        wrapper();",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::CurrentClosure, &[]),
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::Sub, &[]),
                            (Opcode::Call, &[&[1]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        1,
                    ))),
                    Object::Integer(1),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::Closure, &[&[0, 1], &[0], &[]]),
                            (Opcode::SetLocal, &[&[0]]),
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::LoadConstant, &[&[0, 2]]),
                            (Opcode::Call, &[&[1]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 3], &[0], &[]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::GetGlobal, &[&[0, 0]]),
                    (Opcode::Call, &[&[0]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_assignment() {
        let tests = vec![
            CompilerTestCase {
                input: "let a = 2; a = 1;",
                expected_constants: vec![Object::Integer(2), Object::Integer(1)],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                ]),
            },
            CompilerTestCase {
                input: "fn() { let a = 2; a = 1 };",
                expected_constants: vec![
                    Object::Integer(2),
                    Object::Integer(1),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::SetLocal, &[&[0]]),
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::SetLocal, &[&[0]]),
                            (Opcode::Return, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 2], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "let a = [1, 2]; a[0] = 3;",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(0),
                    Object::Integer(3),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::Array, &[&[0, 2]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::GetGlobal, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::LoadConstant, &[&[0, 3]]),
                    (Opcode::AssignIndexable, &[]),
                ]),
            },
            CompilerTestCase {
                input: "fn() {let a = [1, 2]; a[0] = 3;}",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(0),
                    Object::Integer(3),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::Array, &[&[0, 2]]),
                            (Opcode::SetLocal, &[&[0]]),
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::LoadConstant, &[&[0, 2]]),
                            (Opcode::LoadConstant, &[&[0, 3]]),
                            (Opcode::AssignIndexable, &[]),
                            (Opcode::Return, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 4], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "let a = 1; let b = 2; a = 3; b = 4;",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                    Object::Integer(4),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::SetGlobal, &[&[0, 1]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 3]]),
                    (Opcode::SetGlobal, &[&[0, 1]]),
                ]),
            },
            CompilerTestCase {
                input: "let a = 1; fn() { let b = 2; a = 3; b = 4; }",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                    Object::Integer(4),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::SetLocal, &[&[0]]),
                            (Opcode::LoadConstant, &[&[0, 2]]),
                            (Opcode::SetGlobal, &[&[0, 0]]),
                            (Opcode::LoadConstant, &[&[0, 3]]),
                            (Opcode::SetLocal, &[&[0]]),
                            (Opcode::Return, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::Closure, &[&[0, 4], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "let a = 1; let b = fn() { let a = 1; a }; a + b()",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(1),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::SetLocal, &[&[0]]),
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        1,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::Closure, &[&[0, 2], &[0], &[]]),
                    (Opcode::SetGlobal, &[&[0, 1]]),
                    (Opcode::GetGlobal, &[&[0, 0]]),
                    (Opcode::GetGlobal, &[&[0, 1]]),
                    (Opcode::Call, &[&[0]]),
                    (Opcode::Add, &[]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "fn() { let a = 1; let f = fn() { a = 2; a }; f(); a }",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::AssignFree, &[&[0]]),
                            (Opcode::GetFree, &[&[0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::SetLocal, &[&[0]]),
                            (Opcode::Closure, &[&[0, 2], &[1], &[0, 0]]),
                            (Opcode::SetLocal, &[&[1]]),
                            (Opcode::GetLocal, &[&[1]]),
                            (Opcode::Call, &[&[0]]),
                            (Opcode::Pop, &[]),
                            (Opcode::GetLocal, &[&[0]]),
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        2,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 3], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_while_statements() {
        let tests = vec![
            CompilerTestCase {
                input: "while (1 < 2) { 5 + 5 }",
                expected_constants: vec![
                    Object::Integer(2),
                    Object::Integer(1),
                    Object::Integer(5),
                    Object::Integer(5),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::GreaterThan, &[]),
                    (Opcode::JumpNotTruthy, &[&[0, 21]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::LoadConstant, &[&[0, 3]]),
                    (Opcode::Add, &[]),
                    (Opcode::Pop, &[]),
                    (Opcode::Jump, &[&[0, 0]]),
                ]),
            },
            CompilerTestCase {
                input: "while (true) { }",
                expected_constants: vec![],
                expected_instructions: make_instructions(vec![
                    (Opcode::True, &[]),
                    (Opcode::JumpNotTruthy, &[&[0, 7]]),
                    (Opcode::Jump, &[&[0, 0]]),
                ]),
            },
            CompilerTestCase {
                input: "while (1 < 2) { while (3 < 4) { 5 } }",
                expected_constants: vec![
                    Object::Integer(2),
                    Object::Integer(1),
                    Object::Integer(4),
                    Object::Integer(3),
                    Object::Integer(5),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&[0, 0]]),
                    (Opcode::LoadConstant, &[&[0, 1]]),
                    (Opcode::GreaterThan, &[]),
                    (Opcode::JumpNotTruthy, &[&[0, 30]]),
                    (Opcode::LoadConstant, &[&[0, 2]]),
                    (Opcode::LoadConstant, &[&[0, 3]]),
                    (Opcode::GreaterThan, &[]),
                    (Opcode::JumpNotTruthy, &[&[0, 27]]),
                    (Opcode::LoadConstant, &[&[0, 4]]),
                    (Opcode::Pop, &[]),
                    (Opcode::Jump, &[&[0, 10]]),
                    (Opcode::Jump, &[&[0, 0]]),
                ]),
            },
            CompilerTestCase {
                input: "fn() { while (1 < 2) { 3 } }",
                expected_constants: vec![
                    Object::Integer(2),
                    Object::Integer(1),
                    Object::Integer(3),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::GreaterThan, &[]),
                            (Opcode::JumpNotTruthy, &[&[0, 17]]),
                            (Opcode::LoadConstant, &[&[0, 2]]),
                            (Opcode::Pop, &[]),
                            (Opcode::Jump, &[&[0, 0]]),
                            (Opcode::Return, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 3], &[0], &[]]),
                    (Opcode::Pop, &[]),
                ]),
            },
            CompilerTestCase {
                input: "
                    let inner = fn() { 5 };
                    let outer = fn() { while (1 < 2) { inner() } };
                ",
                expected_constants: vec![
                    Object::Integer(5),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]), // 5
                            (Opcode::ReturnValue, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                    Object::Integer(2),
                    Object::Integer(1),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 2]]),
                            (Opcode::LoadConstant, &[&[0, 3]]),
                            (Opcode::GreaterThan, &[]),
                            (Opcode::JumpNotTruthy, &[&[0, 19]]),
                            (Opcode::GetGlobal, &[&[0, 0]]),
                            (Opcode::Call, &[&[0]]),
                            (Opcode::Pop, &[]),
                            (Opcode::Jump, &[&[0, 0]]),
                            (Opcode::Return, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 1], &[0], &[]]), // inner fn
                    (Opcode::SetGlobal, &[&[0, 0]]),          // let inner
                    (Opcode::Closure, &[&[0, 4], &[0], &[]]), // outer fn
                    (Opcode::SetGlobal, &[&[0, 1]]),          // let outer
                ]),
            },
            CompilerTestCase {
                input: "
                    let inner = fn() { while (3 < 4) { 5 } };
                    let outer = fn() { while (1 < 2) { inner() } };
                    outer();
                ",
                expected_constants: vec![
                    Object::Integer(4),
                    Object::Integer(3),
                    Object::Integer(5),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 0]]),
                            (Opcode::LoadConstant, &[&[0, 1]]),
                            (Opcode::GreaterThan, &[]),
                            (Opcode::JumpNotTruthy, &[&[0, 17]]),
                            (Opcode::LoadConstant, &[&[0, 2]]),
                            (Opcode::Pop, &[]),
                            (Opcode::Jump, &[&[0, 0]]),
                            (Opcode::Return, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                    Object::Integer(2),
                    Object::Integer(1),
                    Object::CompiledFunction(Rc::new(CompiledFunction::new(
                        make_instructions(vec![
                            (Opcode::LoadConstant, &[&[0, 4]]),
                            (Opcode::LoadConstant, &[&[0, 5]]),
                            (Opcode::GreaterThan, &[]),
                            (Opcode::JumpNotTruthy, &[&[0, 19]]),
                            (Opcode::GetGlobal, &[&[0, 0]]),
                            (Opcode::Call, &[&[0]]),
                            (Opcode::Pop, &[]),
                            (Opcode::Jump, &[&[0, 0]]),
                            (Opcode::Return, &[]),
                        ])
                        .into_boxed_slice(),
                        0,
                        0,
                    ))),
                ],
                expected_instructions: make_instructions(vec![
                    (Opcode::Closure, &[&[0, 3], &[0], &[]]),
                    (Opcode::SetGlobal, &[&[0, 0]]),
                    (Opcode::Closure, &[&[0, 6], &[0], &[]]),
                    (Opcode::SetGlobal, &[&[0, 1]]),
                    (Opcode::GetGlobal, &[&[0, 1]]),
                    (Opcode::Call, &[&[0]]),
                    (Opcode::Pop, &[]),
                ]),
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_read_operands() {
        struct Test {
            opcode: Opcode,
            operands: &'static [&'static [u8]],
            expected_result: &'static [usize],
            expected_offset: usize,
        }

        let tests = vec![
            Test {
                opcode: Opcode::LoadConstant,
                operands: &[&[0xFF, 0xFF]],
                expected_result: &[65535],
                expected_offset: 2,
            },
            Test {
                opcode: Opcode::GetLocal,
                operands: &[&[0xFF]],
                expected_result: &[255],
                expected_offset: 1,
            },
            Test {
                opcode: Opcode::Closure,
                operands: &[&[0xFF, 0xFF], &[0xFF], &[0xFF]],
                expected_result: &[65535, 255, 255],
                expected_offset: 4,
            },
        ];

        for test in tests {
            let mut instruction = Vec::<u8>::new();
            make(&mut instruction, test.opcode, test.operands);
            let opcode = Opcode::from_byte(instruction[0]);
            let (operands, offset) = read_operand(opcode, &instruction[1..]);

            assert_eq!(
                test.expected_offset, offset,
                "expected {} bytes, got {} bytes",
                test.expected_offset, offset
            );

            for (operand, expected) in operands
                .iter()
                .zip(test.expected_result)
                .collect::<Vec<_>>()
            {
                assert_eq!(
                    expected, operand,
                    "expected operand {:?} got {:?}",
                    expected, operand
                );
            }
        }
    }

    #[test]
    fn test_instructions_formatting() {
        let tests = vec![
            FormattingTestCase {
                instructions: make_instructions(vec![
                    (Opcode::LoadConstant, &[&vec![0x00, 0x01]]),
                    (Opcode::LoadConstant, &[&vec![0x00, 0x02]]),
                    (Opcode::LoadConstant, &[&vec![0xFF, 0xFF]]),
                ]),
                expected: "0000 LoadConstant 1\n0003 LoadConstant 2\n0006 LoadConstant 65535\n",
            },
            FormattingTestCase {
                instructions: make_instructions(vec![
                    (Opcode::Add, &[]),
                    (Opcode::LoadConstant, &[&vec![0x00, 0x02]]),
                    (Opcode::LoadConstant, &[&vec![0xFF, 0xFF]]),
                ]),
                expected: "0000 Add\n0001 LoadConstant 2\n0004 LoadConstant 65535\n",
            },
            FormattingTestCase {
                instructions: make_instructions(vec![
                    (Opcode::Add, &[]),
                    (Opcode::GetLocal, &[&vec![0x01]]),
                    (Opcode::LoadConstant, &[&vec![0x0, 0x02]]),
                    (Opcode::LoadConstant, &[&vec![0xFF, 0xFF]]),
                ]),
                expected: "0000 Add\n0001 GetLocal 1\n0003 LoadConstant 2\n0006 LoadConstant 65535\n",
            },
            FormattingTestCase {
                instructions: make_instructions(vec![
                    (Opcode::Add, &[]),
                    (Opcode::GetLocal, &[&vec![0x01]]),
                    (Opcode::LoadConstant, &[&vec![0x0, 0x02]]),
                    (Opcode::LoadConstant, &[&vec![0xFF, 0xFF]]),
                    (
                        Opcode::Closure,
                        &[&[0xFF, 0xFF], &[0xFF], &[0xFF, 0xFF, 0xFF]],
                    ),
                ]),
                expected: "0000 Add\n0001 GetLocal 1\n0003 LoadConstant 2\n0006 LoadConstant 65535\n0009 Closure 65535 255 255 255 255\n",
            },
        ];

        for test in tests {
            let result = format_instructions(&test.instructions);

            assert_eq!(
                test.expected, result,
                "instructions wrongly formatted expected:\n{}\ngot:\n{}",
                test.expected, result
            );
        }
    }

    #[test]
    fn test_compiler_scopes() -> Result<(), CompilationError> {
        let mut compiler = Compiler::new();

        assert_eq!(
            compiler.scope_index, 0,
            "scope index wrong got: {} want {}",
            compiler.scope_index, 0
        );

        // add all builtins to the global symbol table to mach the one that is created in the
        // compiler
        let global_symbol_table = SymbolTable::new();
        for (i, builtin) in BUILTINS.iter().enumerate() {
            global_symbol_table
                .borrow_mut()
                .define_builtin(i as u16, builtin.name);
        }

        compiler.emit(Opcode::Mul, &[]);

        compiler.enter_scope();

        assert_eq!(
            compiler.scope_index, 1,
            "scope index wrong got: {} want {}",
            compiler.scope_index, 1
        );

        compiler.emit(Opcode::Sub, &[]);

        let mut last = compiler.scopes[compiler.scope_index].last_instruction;

        assert_eq!(
            last.opcode,
            Opcode::Sub,
            "last instruction opcode wrong got {} want {}",
            last.opcode,
            Opcode::Sub
        );

        assert_eq!(
            compiler.symbol_table.borrow().outer.clone().unwrap(),
            global_symbol_table,
            "compiler did not enclose symbolTable"
        );

        compiler.leave_scope();

        assert_eq!(
            compiler.scope_index, 0,
            "scope index wrong got: {} want {}",
            compiler.scope_index, 0
        );

        assert_eq!(
            compiler.symbol_table, global_symbol_table,
            "compiler did not restore global symbol table"
        );

        assert_eq!(
            compiler.symbol_table.borrow().outer,
            None,
            "compiler modified global symbol table incorrectly"
        );

        compiler.emit(Opcode::Add, &[]);

        assert_eq!(
            compiler.scopes[compiler.scope_index].instructions.len(),
            2,
            "instructions length wrong got {} want {}",
            compiler.scopes[compiler.scope_index].instructions.len(),
            2
        );

        last = compiler.scopes[compiler.scope_index].last_instruction;
        assert_eq!(
            last.opcode,
            Opcode::Add,
            "last instruction opcode wrong got {} want {}",
            last.opcode,
            Opcode::Add
        );

        let previous = compiler.scopes[compiler.scope_index].previous_instruction;
        assert_eq!(
            previous.opcode,
            Opcode::Mul,
            "last instruction opcode wrong got {} want {}",
            previous.opcode,
            Opcode::Mul
        );

        Ok(())
    }
}
