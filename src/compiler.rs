use crate::code::{Opcode, make, OPERAND_WIDTHS};
use crate::object::Object;

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

    pub fn compile(&self) {}

    pub fn bytecode(&self) -> Bytecode {
        Bytecode {
            instructions: self.instructions.clone().into_boxed_slice(),
            constants: self.constants.clone().into_boxed_slice(),
        }
    }
}

pub struct Bytecode {
    instructions: Box<[u8]>,
    constants: Box<[Object]>,
}

// Helpers

fn format_instructions(instructions: &[u8]) -> String {
    let mut result = String::new();

    let mut i = 0;
    while i < instructions.len() {
        let adress = i;
        let opcode = Opcode::try_from(instructions[i]).unwrap();
        i += 1; 

        let (operand, offset) = read_operand(opcode.clone(), &instructions[i..]);
        i += offset;

        let instruction_string = format!("{:04} {} {}\n", adress, opcode.clone(), operand);
        result.push_str(&instruction_string);
    }

    result
}

fn read_operand(opcode: Opcode, instructions: &[u8]) -> (usize, usize) {
    let operand_width = OPERAND_WIDTHS[opcode as usize] as usize;
    let val: usize = match operand_width {
        0 => 0,
        1 => instructions[0] as usize,
        2 => {
            u16::from_be_bytes([instructions[0], instructions[1]]) as usize
        }
        _ => panic!("unsopperted opperand width")
    };
    (val, operand_width)
}


#[cfg(test)]
mod tests {
    use crate::{
        ast::Program,
        lexer::Lexer,
        parser::{ParseError, Parser},
    };

    use super::*;

    #[derive(Debug)]
    struct CompilerTestCase {
        input: &'static str,
        expected_constants: Vec<Object>,
        expected_instructions: Vec<Box<[u8]>>,
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
            let compiler = Compiler::new();
            compiler.compile();

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
                "expected instructions {:?} got {:?}",
                &expected_bytes,
                bytecode.instructions.as_ref(),
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
        let tests = vec![CompilerTestCase {
            input: "1 + 2",
            expected_constants: vec![Object::Integer(1), Object::Integer(2)],
            expected_instructions: vec![
                make(Opcode::OpConstant, &vec![0, 0]),
                make(Opcode::OpConstant, &vec![0, 1]),
            ],
        }];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_read_operands() {
        let tests = vec![(Opcode::OpConstant, vec![0xFF, 0xFF], 65535, 2)];

        for (opcode, operand_bytes, expected_result, expected_offset) in tests {
            let instruction = make(opcode, &operand_bytes);
            let opcode = Opcode::try_from(instruction[0]).unwrap();
            let (operand, offset) = read_operand(opcode, &instruction[1..]);

            assert_eq!(expected_offset, offset, "expected {} bytes, got {} bytes", expected_offset, offset);
            assert_eq!(expected_result, operand, "expected operand {:?} got {:?}", expected_result, operand);
        }
    }

    #[test]
    fn test_instructions_formatting() {
        let tests = vec![
            make(Opcode::OpConstant, &vec![0x00, 0x01]),
            make(Opcode::OpConstant, &vec![0x00, 0x02]),
            make(Opcode::OpConstant, &vec![0xFF, 0xFF]),
        ];
        let expected = "0000 OpConstant 1\n0003 OpConstant 2\n0006 OpConstant 65535\n";

        let test_bytes: Vec<u8> = tests
            .iter()
            .flat_map(|instruction| instruction.iter())
            .copied()
            .collect();

        let result = format_instructions(&test_bytes); 
        assert_eq!(expected, result, "instructions wrongly formatted expected:\n{}\ngot:\n{}", expected, result);
    }
}

