use crate::ast::{Expression, Program, Statement};
use crate::code::{OPERAND_WIDTHS, Opcode, make};
use crate::object::Object;

#[derive(Debug)]
pub enum CompilationError {
    Generic(String),
    UnkownOpcode(u8),
    UnknownOperator(String),
}

pub struct Compiler {
    instructions: Vec<u8>,
    constants: Vec<Object>,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            instructions: Vec::<u8>::new(),
            constants: Vec::<Object>::new(),
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
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn compile_expression(&mut self, expression: &Expression) -> Result<(), CompilationError> {
        match expression {
            Expression::IntegerLiteral(integer_literal_expression) => {
                let integer = Object::Integer(integer_literal_expression.value);
                let position = self.add_constant(integer);
                self.emit(Opcode::LoadConstant, &position.to_be_bytes());
                Ok(())
            }
            Expression::Infix(infix_expression) => {
                self.compile_expression(&infix_expression.left)?;
                self.compile_expression(&infix_expression.right)?;

                let operator = infix_expression.token.literal.as_str();
                match operator {
                    "+" => self.emit(Opcode::Add, &[]),
                    "-" => self.emit(Opcode::Sub, &[]),
                    "*" => self.emit(Opcode::Mul, &[]),
                    "/" => self.emit(Opcode::Div, &[]),
                    _ => return Err(CompilationError::UnknownOperator(operator.to_string())),
                };

                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn emit(&mut self, opcode: Opcode, operand: &[u8]) -> usize {
        let instruction = make(opcode, operand);
        let position = self.add_instruction(instruction.as_ref());
        position
    }

    pub fn bytecode(&self) -> Bytecode {
        Bytecode {
            instructions: self.instructions.clone().into_boxed_slice(),
            constants: self.constants.clone().into_boxed_slice(),
        }
    }
}

pub struct Bytecode {
    pub instructions: Box<[u8]>,
    pub constants: Box<[Object]>,
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
    let operand_width = OPERAND_WIDTHS[opcode as usize] as usize;
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
                &expected_bytes,
                bytecode.instructions.as_ref(),
                "expected instructions:\n{}got:\n{}",
                format_instructions(&expected_bytes),
                format_instructions(bytecode.instructions.as_ref()),
            );

            assert_eq!(
                &test.expected_constants,
                bytecode.constants.as_ref(),
                "expected constants {:?} got {:?}",
                &test.expected_constants,
                bytecode.constants.as_ref(),
            );
        }
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
        ];

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
}
