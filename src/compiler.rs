use crate::code::{Opcode, make};
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
    result
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
    fn test_instructions_formatting() {
        let tests = vec![
            make(Opcode::OpConstant, &vec![0x00, 0x01]),
            make(Opcode::OpConstant, &vec![0x00, 0x02]),
            make(Opcode::OpConstant, &vec![0xFF, 0xFF]),
        ];
        let expected = "0000 OpConstant 1\n0003 OpConstant 2\n0006 OpConstant 65535";

        let test_bytes: Vec<u8> = tests
            .iter()
            .flat_map(|instruction| instruction.iter())
            .copied()
            .collect();

        let result = format_instructions(&test_bytes); 
        assert_eq!(expected, result, "instructions wrongly formatted expected:\n{}\ngot:\n {}", expected, result);
    }
}

