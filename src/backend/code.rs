use std::{
    alloc::{Layout, alloc},
    fmt,
};

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq)]
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
    JumpNotTruthy = 0xD,
    Jump = 0xE,
    Null = 0xF,
    GetGlobal = 0x10,
    SetGlobal = 0x11,
    Array = 0x12,
    Hash = 0x13,
    Index = 0x14,
    Call = 0x15,
    ReturnValue = 0x16,
    Return = 0x17,
}

impl Opcode {
    pub fn from_byte(value: u8) -> Opcode {
        match value {
            0x00 => Opcode::LoadConstant,
            0x01 => Opcode::Add,
            0x02 => Opcode::Sub,
            0x03 => Opcode::Mul,
            0x04 => Opcode::Div,
            0x05 => Opcode::Pop,
            0x06 => Opcode::True,
            0x07 => Opcode::False,
            0x08 => Opcode::Equal,
            0x09 => Opcode::NotEqual,
            0x0A => Opcode::GreaterThan,
            0x0B => Opcode::Minus,
            0x0C => Opcode::Bang,
            0x0D => Opcode::JumpNotTruthy,
            0x0E => Opcode::Jump,
            0x0F => Opcode::Null,
            0x10 => Opcode::GetGlobal,
            0x11 => Opcode::SetGlobal,
            0x12 => Opcode::Array,
            0x13 => Opcode::Hash,
            0x14 => Opcode::Index,
            0x15 => Opcode::Call,
            0x16 => Opcode::ReturnValue,
            0x17 => Opcode::Return,
            _ => unreachable!("unsupported opcode {}", value),
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
            Opcode::JumpNotTruthy => "JumpNotTruthy",
            Opcode::Jump => "Jump",
            Opcode::Null => "Null",
            Opcode::GetGlobal => "GetGlobal",
            Opcode::SetGlobal => "SetGlobal",
            Opcode::Array => "Array",
            Opcode::Hash => "Hash",
            Opcode::Index => "Index",
            Opcode::Call => "Call",
            Opcode::ReturnValue => "ReturnValue",
            Opcode::Return => "Return",
        };
        write!(f, "{}", name)
    }
}

const fn build_operand_widths() -> [usize; 256] {
    let mut table = [0usize; 256];
    table[Opcode::LoadConstant as usize] = 2;
    table[Opcode::Add as usize] = 0;
    table[Opcode::Sub as usize] = 0;
    table[Opcode::Mul as usize] = 0;
    table[Opcode::Div as usize] = 0;
    table[Opcode::Pop as usize] = 0;
    table[Opcode::True as usize] = 0;
    table[Opcode::False as usize] = 0;
    table[Opcode::Equal as usize] = 0;
    table[Opcode::NotEqual as usize] = 0;
    table[Opcode::GreaterThan as usize] = 0;
    table[Opcode::Minus as usize] = 0;
    table[Opcode::Bang as usize] = 0;
    table[Opcode::JumpNotTruthy as usize] = 2;
    table[Opcode::Jump as usize] = 2;
    table[Opcode::Null as usize] = 0;
    table[Opcode::GetGlobal as usize] = 2;
    table[Opcode::SetGlobal as usize] = 2;
    table[Opcode::Array as usize] = 2;
    table[Opcode::Hash as usize] = 2;
    table[Opcode::Index as usize] = 0;
    table[Opcode::Call as usize] = 0;
    table[Opcode::ReturnValue as usize] = 0;
    table[Opcode::Return as usize] = 0;
    table
}

pub static OPERAND_WIDTHS: [usize; 256] = build_operand_widths();

pub fn make(opcode: Opcode, operand: &[u8]) -> Box<[u8]> {
    debug_assert_eq!(
        operand.len(),
        OPERAND_WIDTHS[opcode as usize],
        "operand {:?} does not have correct width for opcode {}",
        operand,
        opcode
    );

    let instruction_length = 1 + operand.len();
    let mut instruction = allocate_array(instruction_length);
    let instruction_slice = instruction.as_mut();

    instruction_slice[0] = opcode as u8;
    instruction_slice[1..].copy_from_slice(operand);

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
