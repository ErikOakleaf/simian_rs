use std::collections::HashMap;

use crate::ast::{BlockStatement, Expression, Program, Statement};
use crate::code::{OPERAND_WIDTHS, Opcode, make};
use crate::object::Object;

#[derive(Debug)]
pub enum CompilationError {
    UnknownOpcode(u8),
    UnknownOperator(String),
    UnknownSymbol(String),
    Other(String),
}

#[derive(Clone, Copy)]
struct EmittedInstruction {
    opcode: Opcode,
    position: usize,
}

pub struct Compiler {
    instructions: Vec<u8>,
    pub constants: Vec<Object>,

    last_intstruction: EmittedInstruction,
    previous_instruction: EmittedInstruction,

    pub symbol_table: SymbolTable,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            instructions: Vec::<u8>::new(),
            constants: Vec::<Object>::new(),

            last_intstruction: EmittedInstruction {
                opcode: Opcode::LoadConstant,
                position: 0,
            },
            previous_instruction: EmittedInstruction {
                opcode: Opcode::LoadConstant,
                position: 0,
            },
            symbol_table: SymbolTable::new(),
        }
    }

    pub fn new_with_state(symbol_table: SymbolTable, constants: Vec<Object>) -> Self {
        Compiler {
            instructions: Vec::<u8>::new(),
            constants: constants,

            last_intstruction: EmittedInstruction {
                opcode: Opcode::LoadConstant,
                position: 0,
            },
            previous_instruction: EmittedInstruction {
                opcode: Opcode::LoadConstant,
                position: 0,
            },
            symbol_table: symbol_table,
        }
    }

    fn add_constant(&mut self, object: Object) -> u16 {
        self.constants.push(object);
        (self.constants.len() - 1) as u16
    }

    fn add_instruction(&mut self, instruction: &[u8]) -> usize {
        let position = self.instructions.len();
        self.instructions.extend_from_slice(instruction);
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
                self.compile_expression(let_statement.value.as_ref())?;
                let symbol = self.symbol_table.define(&let_statement.name.token.literal);
                self.emit(Opcode::SetGlobal, &symbol.index.to_be_bytes());
            }
            _ => {}
        };
        Ok(())
    }

    fn compile_expression(&mut self, expression: &Expression) -> Result<(), CompilationError> {
        match expression {
            Expression::IntegerLiteral(integer_literal_expression) => {
                let integer = Object::Integer(integer_literal_expression.value);
                let position = self.add_constant(integer);
                self.emit(Opcode::LoadConstant, &position.to_be_bytes());
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
                let index = {
                    let symbol = self
                        .symbol_table
                        .resolve(&identifier_expression.token.literal)?;
                    symbol.index
                };
                self.emit(Opcode::GetGlobal, &index.to_be_bytes());
            }
            Expression::String(string_token) => {
                let string_object = Object::String(string_token.literal.clone());
                let index = self.add_constant(string_object).to_be_bytes();
                self.emit(Opcode::LoadConstant, &index);
            }
            Expression::Array(array_literal_expression) => {
                for element in array_literal_expression.elements.iter() {
                    self.compile_expression(element)?;
                }

                let length = array_literal_expression.elements.len() as u16;
                let length_bytes = length.to_be_bytes();
                self.emit(Opcode::Array, &length_bytes);
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
                self.emit(Opcode::Hash, &length_bytes);
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

                let jump_not_truthy_position = self.emit(Opcode::JumpNotTruthy, &[0xFF, 0xFF]);

                self.compile_block_statement(&if_expression.consequence)?;

                if self.last_intstruction.opcode == Opcode::Pop {
                    self.remove_last_pop();
                }

                let jump_position = self.emit(Opcode::Jump, &[0xFF, 0xFF]);
                let after_consequence_position = self.get_current_position();
                self.change_operand(jump_not_truthy_position, &after_consequence_position)?;

                match &if_expression.alternative {
                    None => {
                        self.emit(Opcode::Null, &[]);
                    }
                    Some(alternative) => {
                        self.compile_block_statement(alternative)?;

                        if self.last_intstruction.opcode == Opcode::Pop {
                            self.remove_last_pop();
                        }
                    }
                };

                let after_alternative_position = self.get_current_position();
                self.change_operand(jump_position, &after_alternative_position)?;
            }
            Expression::Index(index_expression) => {
                self.compile_expression(index_expression.left.as_ref())?;
                self.compile_expression(index_expression.index.as_ref())?;
                self.emit(Opcode::Index, &[]);
            }
            _ => {}
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

    fn emit(&mut self, opcode: Opcode, operand: &[u8]) -> usize {
        let instruction = make(opcode, operand);
        let position = self.add_instruction(instruction.as_ref());

        self.set_last_instruction(opcode, position);

        position
    }

    pub fn bytecode(&self) -> Bytecode {
        Bytecode {
            instructions: self.instructions.clone().into_boxed_slice(),
            constants: self.constants.clone().into_boxed_slice(),
        }
    }

    // Helpers

    #[inline]
    fn set_last_instruction(&mut self, opcode: Opcode, position: usize) {
        self.previous_instruction = self.last_intstruction;
        self.last_intstruction = EmittedInstruction {
            opcode: opcode,
            position: position,
        }
    }

    #[inline]
    fn change_operand(
        &mut self,
        opcode_position: usize,
        new_operand: &[u8],
    ) -> Result<(), CompilationError> {
        let opcode = Opcode::try_from(self.instructions[opcode_position])?;

        if new_operand.len() != OPERAND_WIDTHS[opcode as usize] {
            return Err(CompilationError::Other(
                "New operand is not the correct ammount of bytes".to_string(),
            ));
        }

        let operand_position = opcode_position + 1;

        for (i, byte) in new_operand.iter().enumerate() {
            self.instructions[operand_position + i] = *byte;
        }

        Ok(())
    }

    #[inline(always)]
    fn remove_last_pop(&mut self) {
        self.instructions.pop();
    }

    #[inline(always)]
    fn get_current_position(&self) -> [u8; 2] {
        let after_consequence_position = self.instructions.len() as u16;
        after_consequence_position.to_be_bytes()
    }
}

pub struct Bytecode {
    pub instructions: Box<[u8]>,
    pub constants: Box<[Object]>,
}

#[derive(Clone, Debug, PartialEq)]
enum SymbolScope {
    Global,
    Local,
}

#[derive(Clone, Debug, PartialEq)]
struct Symbol {
    name: String,
    scope: SymbolScope,
    index: u16,
}

#[derive(Clone, Debug, PartialEq)]
pub struct SymbolTable {
    store: HashMap<String, Symbol>,
    amount_definitons: usize,
}

impl SymbolTable {
    pub fn new() -> Self {
        SymbolTable {
            store: HashMap::<String, Symbol>::new(),
            amount_definitons: 0,
        }
    }

    fn define(&mut self, name: &str) -> Symbol {
        let symbol = Symbol {
            name: name.to_string(),
            scope: SymbolScope::Global,
            index: self.amount_definitons as u16,
        };
        self.store.insert(name.to_string(), symbol.clone());
        self.amount_definitons += 1;
        symbol
    }

    fn resolve(&mut self, name: &str) -> Result<&Symbol, CompilationError> {
        self.store
            .get(name)
            .ok_or_else(|| CompilationError::UnknownSymbol(name.to_string()))
    }
}

// Helpers

fn format_instructions(instructions: &[u8]) -> String {
    let mut result = String::new();

    let mut i = 0;
    while i < instructions.len() {
        let address = i;
        let opcode = Opcode::try_from(instructions[i])
            .expect(&format!("opcode not supported {}", instructions[i]));
        i += 1;

        let (operand, offset) = read_operand(opcode.clone(), &instructions[i..]);
        i += offset;

        let instruction_string = match operand {
            Some(val) => format!("{:04} {} {}\n", address, opcode, val),
            None => format!("{:04} {}\n", address, opcode),
        };

        result.push_str(&instruction_string);
    }

    result
}

fn read_operand(opcode: Opcode, instructions: &[u8]) -> (Option<usize>, usize) {
    let operand_width = OPERAND_WIDTHS[opcode as usize];
    let val: Option<usize> = match operand_width {
        0 => None,
        1 => Some(instructions[0] as usize),
        2 => Some(u16::from_be_bytes([instructions[0], instructions[1]]) as usize),
        _ => panic!("unsopperted opperand width"),
    };
    (val, operand_width)
}

#[cfg(test)]
mod tests {
    use crate::{ast::Program, lexer::Lexer, parser::Parser};

    use super::*;

    #[derive(Debug)]
    struct CompilerTestCase {
        input: &'static str,
        expected_constants: Vec<Object>,
        expected_instructions: Vec<Box<[u8]>>,
    }

    struct FormattingTestCase {
        instructions: Vec<Box<[u8]>>,
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
            let expected_bytes: Vec<u8> = test
                .expected_instructions
                .iter()
                .flat_map(|instruction| instruction.iter())
                .copied()
                .collect();

            assert_eq!(
                &test.expected_constants,
                bytecode.constants.as_ref(),
                "expected constants {:?} got {:?}",
                &test.expected_constants,
                bytecode.constants.as_ref(),
            );

            assert_eq!(
                &expected_bytes,
                bytecode.instructions.as_ref(),
                "expected instructions:\n{}got:\n{}",
                format_instructions(&expected_bytes),
                format_instructions(bytecode.instructions.as_ref()),
            );
        }
    }

    // Tests

    #[test]
    fn test_integer_arithmetic() {
        let tests = vec![
            CompilerTestCase {
                input: "1 + 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &vec![0, 0]),
                    make(Opcode::LoadConstant, &vec![0, 1]),
                    make(Opcode::Add, &vec![]),
                    make(Opcode::Pop, &vec![]),
                ],
            },
            CompilerTestCase {
                input: "1; 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &vec![0, 0]),
                    make(Opcode::Pop, &vec![]),
                    make(Opcode::LoadConstant, &vec![0, 1]),
                    make(Opcode::Pop, &vec![]),
                ],
            },
            CompilerTestCase {
                input: "1 - 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &vec![0, 0]),
                    make(Opcode::LoadConstant, &vec![0, 1]),
                    make(Opcode::Sub, &vec![]),
                    make(Opcode::Pop, &vec![]),
                ],
            },
            CompilerTestCase {
                input: "1 * 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &vec![0, 0]),
                    make(Opcode::LoadConstant, &vec![0, 1]),
                    make(Opcode::Mul, &vec![]),
                    make(Opcode::Pop, &vec![]),
                ],
            },
            CompilerTestCase {
                input: "2 / 1",
                expected_constants: vec![Object::Integer(2), Object::Integer(1)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &vec![0, 0]),
                    make(Opcode::LoadConstant, &vec![0, 1]),
                    make(Opcode::Div, &vec![]),
                    make(Opcode::Pop, &vec![]),
                ],
            },
            CompilerTestCase {
                input: "-1",
                expected_constants: vec![Object::Integer(1)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &vec![0, 0]),
                    make(Opcode::Minus, &vec![]),
                    make(Opcode::Pop, &vec![]),
                ],
            },
            CompilerTestCase {
                input: "!true",
                expected_constants: vec![],
                expected_instructions: vec![
                    make(Opcode::True, &vec![]),
                    make(Opcode::Bang, &vec![]),
                    make(Opcode::Pop, &vec![]),
                ],
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
                expected_instructions: vec![make(Opcode::True, &[]), make(Opcode::Pop, &[])],
            },
            CompilerTestCase {
                input: "false",
                expected_constants: vec![],
                expected_instructions: vec![make(Opcode::False, &[]), make(Opcode::Pop, &[])],
            },
            CompilerTestCase {
                input: "1 > 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0x00, 0x00]),
                    make(Opcode::LoadConstant, &[0x00, 0x01]),
                    make(Opcode::GreaterThan, &[]),
                    make(Opcode::Pop, &[]),
                ],
            },
            CompilerTestCase {
                input: "1 < 2",
                expected_constants: vec![Object::Integer(2), Object::Integer(1)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0x00, 0x00]),
                    make(Opcode::LoadConstant, &[0x00, 0x01]),
                    make(Opcode::GreaterThan, &[]),
                    make(Opcode::Pop, &[]),
                ],
            },
            CompilerTestCase {
                input: "1 == 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0x00, 0x00]),
                    make(Opcode::LoadConstant, &[0x00, 0x01]),
                    make(Opcode::Equal, &[]),
                    make(Opcode::Pop, &[]),
                ],
            },
            CompilerTestCase {
                input: "1 != 2",
                expected_constants: vec![Object::Integer(1), Object::Integer(2)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0x00, 0x00]),
                    make(Opcode::LoadConstant, &[0x00, 0x01]),
                    make(Opcode::NotEqual, &[]),
                    make(Opcode::Pop, &[]),
                ],
            },
            CompilerTestCase {
                input: "true == false",
                expected_constants: vec![],
                expected_instructions: vec![
                    make(Opcode::True, &[]),
                    make(Opcode::False, &[]),
                    make(Opcode::Equal, &[]),
                    make(Opcode::Pop, &[]),
                ],
            },
            CompilerTestCase {
                input: "true != false",
                expected_constants: vec![],
                expected_instructions: vec![
                    make(Opcode::True, &[]),
                    make(Opcode::False, &[]),
                    make(Opcode::NotEqual, &[]),
                    make(Opcode::Pop, &[]),
                ],
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
                expected_instructions: vec![
                    make(Opcode::True, &[]),
                    make(Opcode::JumpNotTruthy, &[0x00, 10]),
                    make(Opcode::LoadConstant, &[0x00, 0x00]),
                    make(Opcode::Jump, &[0, 11]),
                    make(Opcode::Null, &[]),
                    make(Opcode::Pop, &[]),
                    make(Opcode::LoadConstant, &[0x00, 0x01]),
                    make(Opcode::Pop, &[]),
                ],
            },
            CompilerTestCase {
                input: "if (true) { 10 } else { 20 }; 3333",
                expected_constants: vec![
                    Object::Integer(10),
                    Object::Integer(20),
                    Object::Integer(3333),
                ],
                expected_instructions: vec![
                    make(Opcode::True, &[]),
                    make(Opcode::JumpNotTruthy, &[0x00, 10]),
                    make(Opcode::LoadConstant, &[0x00, 0x00]),
                    make(Opcode::Jump, &[0x00, 13]),
                    make(Opcode::LoadConstant, &[0x00, 0x01]),
                    make(Opcode::Pop, &[]),
                    make(Opcode::LoadConstant, &[0x00, 0x02]),
                    make(Opcode::Pop, &[]),
                ],
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
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0, 0]),
                    make(Opcode::SetGlobal, &[0, 0]),
                    make(Opcode::LoadConstant, &[0, 1]),
                    make(Opcode::SetGlobal, &[0, 1]),
                ],
            },
            CompilerTestCase {
                input: "let one = 1; one;",
                expected_constants: vec![Object::Integer(1)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0, 0]),
                    make(Opcode::SetGlobal, &[0, 0]),
                    make(Opcode::GetGlobal, &[0, 0]),
                    make(Opcode::Pop, &[]),
                ],
            },
            CompilerTestCase {
                input: "let one = 1; let two = one; two;",
                expected_constants: vec![Object::Integer(1)],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0, 0]),
                    make(Opcode::SetGlobal, &[0, 0]),
                    make(Opcode::GetGlobal, &[0, 0]),
                    make(Opcode::SetGlobal, &[0, 1]),
                    make(Opcode::GetGlobal, &[0, 1]),
                    make(Opcode::Pop, &[]),
                ],
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_string_expression() {
        let tests = vec![
            CompilerTestCase {
                input: "\"monkey\"",
                expected_constants: vec![Object::String("monkey".to_string())],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0, 0]),
                    make(Opcode::Pop, &[]),
                ],
            },
            CompilerTestCase {
                input: "\"mon\" + \"key\"",
                expected_constants: vec![
                    Object::String("mon".to_string()),
                    Object::String("key".to_string()),
                ],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0, 0]),
                    make(Opcode::LoadConstant, &[0, 1]),
                    make(Opcode::Add, &[]),
                    make(Opcode::Pop, &[]),
                ],
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
                expected_instructions: vec![make(Opcode::Array, &[0, 0]), make(Opcode::Pop, &[])],
            },
            CompilerTestCase {
                input: "[1, 2, 3]",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(3),
                ],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0, 0]),
                    make(Opcode::LoadConstant, &[0, 1]),
                    make(Opcode::LoadConstant, &[0, 2]),
                    make(Opcode::Array, &[0, 3]),
                    make(Opcode::Pop, &[]),
                ],
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
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0, 0]),
                    make(Opcode::LoadConstant, &[0, 1]),
                    make(Opcode::Add, &[]),
                    make(Opcode::LoadConstant, &[0, 2]),
                    make(Opcode::LoadConstant, &[0, 3]),
                    make(Opcode::Sub, &[]),
                    make(Opcode::LoadConstant, &[0, 4]),
                    make(Opcode::LoadConstant, &[0, 5]),
                    make(Opcode::Mul, &[]),
                    make(Opcode::Array, &[0, 3]),
                    make(Opcode::Pop, &[]),
                ],
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
                expected_instructions: vec![make(Opcode::Hash, &[0, 0]), make(Opcode::Pop, &[])],
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
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0, 0]),
                    make(Opcode::LoadConstant, &[0, 1]),
                    make(Opcode::LoadConstant, &[0, 2]),
                    make(Opcode::LoadConstant, &[0, 3]),
                    make(Opcode::LoadConstant, &[0, 4]),
                    make(Opcode::LoadConstant, &[0, 5]),
                    make(Opcode::Hash, &[0, 6]),
                    make(Opcode::Pop, &[]),
                ],
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
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0, 0]),
                    make(Opcode::LoadConstant, &[0, 1]),
                    make(Opcode::LoadConstant, &[0, 2]),
                    make(Opcode::Add, &[]),
                    make(Opcode::LoadConstant, &[0, 3]),
                    make(Opcode::LoadConstant, &[0, 4]),
                    make(Opcode::LoadConstant, &[0, 5]),
                    make(Opcode::Mul, &[]),
                    make(Opcode::Hash, &[0, 4]),
                    make(Opcode::Pop, &[]),
                ],
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
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0, 0]),
                    make(Opcode::LoadConstant, &[0, 1]),
                    make(Opcode::LoadConstant, &[0, 2]),
                    make(Opcode::Array, &[0, 3]),
                    make(Opcode::LoadConstant, &[0, 3]),
                    make(Opcode::LoadConstant, &[0, 4]),
                    make(Opcode::Add, &[]),
                    make(Opcode::Index, &[]),
                    make(Opcode::Pop, &[]),
                ],
            },
            CompilerTestCase {
                input: "{1: 2}[2 - 1]",
                expected_constants: vec![
                    Object::Integer(1),
                    Object::Integer(2),
                    Object::Integer(2),
                    Object::Integer(1),
                ],
                expected_instructions: vec![
                    make(Opcode::LoadConstant, &[0, 0]),
                    make(Opcode::LoadConstant, &[0, 1]),
                    make(Opcode::Hash, &[0, 2]),
                    make(Opcode::LoadConstant, &[0, 2]),
                    make(Opcode::LoadConstant, &[0, 3]),
                    make(Opcode::Sub, &[]),
                    make(Opcode::Index, &[]),
                    make(Opcode::Pop, &[]),
                ],
            },
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_functions() {
        let tests = vec![CompilerTestCase {
            input: "fn() { return 5 + 10 }",
            expected_constants: vec![
                Object::Integer(5),
                Object::Integer(10),
                Object::CompiledFunction(
                    vec![
                        make(Opcode::LoadConstant, &[0, 0]),
                        make(Opcode::LoadConstant, &[0, 1]),
                        make(Opcode::Add, &[]),
                        make(Opcode::ReturnValue, &[]),
                    ]
                    .into_iter()
                    .flat_map(|b| b.into_vec())
                    .collect::<Vec<u8>>()
                    .into_boxed_slice(),
                ),
            ],
            expected_instructions: vec![
                make(Opcode::LoadConstant, &[0, 2]),
                make(Opcode::Pop, &[]),
            ],
        }];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_read_operands() {
        let tests = vec![(Opcode::LoadConstant, vec![0xFF, 0xFF], 65535, 2)];

        for (opcode, operand_bytes, expected_result, expected_offset) in tests {
            let instruction = make(opcode, &operand_bytes);
            let opcode = Opcode::try_from(instruction[0]).unwrap();
            let (operand, offset) = read_operand(opcode, &instruction[1..]);

            assert_eq!(
                expected_offset, offset,
                "expected {} bytes, got {} bytes",
                expected_offset, offset
            );
            assert_eq!(
                expected_result,
                operand.unwrap(),
                "expected operand {:?} got {:?}",
                expected_result,
                operand.unwrap()
            );
        }
    }

    #[test]
    fn test_instructions_formatting() {
        let tests = vec![
            FormattingTestCase {
                instructions: vec![
                    make(Opcode::LoadConstant, &vec![0x00, 0x01]),
                    make(Opcode::LoadConstant, &vec![0x00, 0x02]),
                    make(Opcode::LoadConstant, &vec![0xFF, 0xFF]),
                ],
                expected: "0000 LoadConstant 1\n0003 LoadConstant 2\n0006 LoadConstant 65535\n",
            },
            FormattingTestCase {
                instructions: vec![
                    make(Opcode::Add, &vec![]),
                    make(Opcode::LoadConstant, &vec![0x00, 0x02]),
                    make(Opcode::LoadConstant, &vec![0xFF, 0xFF]),
                ],
                expected: "0000 Add\n0001 LoadConstant 2\n0004 LoadConstant 65535\n",
            },
        ];

        for test in tests {
            let test_bytes: Vec<u8> = test
                .instructions
                .iter()
                .flat_map(|instruction| instruction.iter())
                .copied()
                .collect();

            let result = format_instructions(&test_bytes);

            assert_eq!(
                test.expected, result,
                "instructions wrongly formatted expected:\n{}\ngot:\n{}",
                test.expected, result
            );
        }
    }

    #[test]
    fn test_define() {
        let tests = vec![
            (
                "a",
                Symbol {
                    name: "a".to_string(),
                    scope: SymbolScope::Global,
                    index: 0,
                },
            ),
            (
                "b",
                Symbol {
                    name: "b".to_string(),
                    scope: SymbolScope::Global,
                    index: 1,
                },
            ),
        ];

        let mut global = SymbolTable::new();

        let symbols = [global.define("a"), global.define("b")];

        for (i, test) in tests.iter().enumerate() {
            assert_eq!(test.1, symbols[i]);
        }
    }

    #[test]
    fn test_resolve_global() -> Result<(), CompilationError> {
        let tests = vec![
            (
                "a",
                Symbol {
                    name: "a".to_string(),
                    scope: SymbolScope::Global,
                    index: 0,
                },
            ),
            (
                "b",
                Symbol {
                    name: "b".to_string(),
                    scope: SymbolScope::Global,
                    index: 1,
                },
            ),
        ];

        let mut global = SymbolTable::new();

        global.define("a");
        global.define("b");

        for test in tests {
            let symbol = global.resolve(test.0)?;
            assert_eq!(test.1, *symbol);
        }

        Ok(())
    }
}
