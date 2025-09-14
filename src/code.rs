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
    Sub = 0x02,
    Mul = 0x03,
    Div = 0x04,
    Pop = 0x05,
    True = 0x06,
    False = 0x07,
    Equal = 0x08,
    NotEqual = 0x09,
    GreaterThan = 0xA,
    Minus = 0xB,
    Bang = 0xC,
}

impl TryFrom<u8> for Opcode {
    type Error = CompilationError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0x00 => Ok(Opcode::LoadConstant),
            0x01 => Ok(Opcode::Add),
            0x02 => Ok(Opcode::Sub),
            0x03 => Ok(Opcode::Mul),
            0x04 => Ok(Opcode::Div),
            0x05 => Ok(Opcode::Pop),
            0x06 => Ok(Opcode::True),
            0x07 => Ok(Opcode::False),
            0x08 => Ok(Opcode::Equal),
            0x09 => Ok(Opcode::NotEqual),
            0x0A => Ok(Opcode::GreaterThan),
            0x0B => Ok(Opcode::Minus),
            0x0C => Ok(Opcode::Bang),
            _ => Err(CompilationError::UnkownOpcode(value)),
        }
    }
}

impl fmt::Display for Opcode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Opcode::LoadConstant => "LoadConstant",
            Opcode::Add => "Add",
            Opcode::Sub => "Sub",
            Opcode::Mul => "Mul",
            Opcode::Div => "Div",
            Opcode::Pop => "Pop",
            Opcode::True => "True",
            Opcode::False => "False",
            Opcode::Equal => "Equal",
            Opcode::NotEqual => "NotEqual",
            Opcode::GreaterThan => "GreaterThan",
            Opcode::Minus => "Minus",
            Opcode::Bang => "Bang",
        };
        write!(f, "{}", name)
    }
}

const fn build_operand_widths() -> [u8; 256] {
    let mut table = [0u8; 256];
    table[Opcode::LoadConstant as usize] = 2;
    table[Opcode::Add as usize] = 0;
    table[Opcode::Sub as usize] = 0;
    table[Opcode::Mul as usize] = 0;
    table[Opcode::Div as usize] = 0;
    table[Opcode::Pop as usize] = 0;
    table[Opcode::Equal as usize] = 0;
    table[Opcode::NotEqual as usize] = 0;
    table[Opcode::GreaterThan as usize] = 0;
    table[Opcode::Minus as usize] = 0;
    table[Opcode::Bang as usize] = 0;
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
