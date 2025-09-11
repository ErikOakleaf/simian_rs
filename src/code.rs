use std::{
    alloc::{Layout, alloc},
    fmt,
};

use crate::compiler::CompilationError;

#[repr(u8)]
#[derive(Clone, Debug)]
pub enum Opcode {
    LoadConstant = 0x00,
    Add = 0x01,
}

impl TryFrom<u8> for Opcode {
    type Error = CompilationError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0x00 => Ok(Opcode::LoadConstant),
            0x01 => Ok(Opcode::Add),
            _ => Err(CompilationError::UnkownOpcode(value)),
        }
    }
}

impl fmt::Display for Opcode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Opcode::LoadConstant => "LoadConstant",
            Opcode::Add => "Add",
        };
        write!(f, "{}", name)
    }
}

const fn build_operand_widths() -> [u8; 256] {
    let mut table = [0u8; 256];
    table[Opcode::LoadConstant as usize] = 2;
    table[Opcode::Add as usize] = 0;
    table
}

pub static OPERAND_WIDTHS: [u8; 256] = build_operand_widths();

pub fn make(opcode: Opcode, operands: &[u8]) -> Box<[u8]> {
    let instruction_length: usize = 1 + operands.len();
    let mut instruction = allocate_array(instruction_length);
    let instruction_slice = instruction.as_mut();

    instruction_slice[0] = opcode as u8;
    instruction_slice[1..].copy_from_slice(operands);

    instruction
}

// Helpers
fn allocate_array(size: usize) -> Box<[u8]> {
    if size == 0 {
        return Box::new([]);
    }

    unsafe {
        let layout = Layout::array::<u8>(size).unwrap();

        let ptr = alloc(layout);

        if ptr.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        Box::from_raw(std::slice::from_raw_parts_mut(ptr, size))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct MakeTestCase<'a> {
        opcode: Opcode,
        operand: &'a [u8],
        expected: &'a [u8],
    }

    #[test]
    fn test_make() {
        let tests = [
            MakeTestCase {
                opcode: Opcode::LoadConstant,
                operand: &[0xFF, 0xFE],
                expected: &[0x00, 0xFF, 0xFE],
            },
            MakeTestCase {
                opcode: Opcode::Add,
                operand: &[],
                expected: &[Opcode::Add as u8],
            },
        ];

        for test in tests {
            let instruction = make(test.opcode, test.operand);

            let instruction_length = instruction.len();
            let expected_length = test.expected.len();
            assert_eq!(
                instruction_length, expected_length,
                "expected instruction length {} got {}",
                expected_length, instruction_length
            );
            assert_eq!(
                instruction.as_ref(),
                test.expected,
                "expected instruction {:?} got {:?}",
                test.expected,
                instruction
            );
        }
    }
}
