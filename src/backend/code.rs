use std::fmt;

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
    GetLocal = 0x18,
    SetLocal = 0x19,
    GetBuiltin = 0x1A,
    Closure = 0x1B,
    GetFree = 0x1C,
    CurrentClosure = 0x1D,
    AssignIndexable = 0x1E,
    AssignFree = 0x1F,
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
            0x18 => Opcode::GetLocal,
            0x19 => Opcode::SetLocal,
            0x1A => Opcode::GetLocal,
            0x1B => Opcode::Closure,
            0x1C => Opcode::GetFree,
            0x1D => Opcode::CurrentClosure,
            0x1E => Opcode::AssignIndexable,
            0x1F => Opcode::AssignFree,
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
            Opcode::GetLocal => "GetLocal",
            Opcode::SetLocal => "SetLocal",
            Opcode::GetBuiltin => "GetBuiltin",
            Opcode::Closure => "Closure",
            Opcode::GetFree => "GetFree",
            Opcode::CurrentClosure => "CurrentClosure",
            Opcode::AssignIndexable => "AssignIndexable",
            Opcode::AssignFree => "AssignFree",
        };
        write!(f, "{}", name)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct OperandInfo {
    pub amount: usize,
    pub widths: &'static [usize],
}

const fn build_operand_widths() -> [OperandInfo; 32] {
    let empty_width: &[usize] = &[];
    let default_operand = OperandInfo {
        amount: 0,
        widths: empty_width,
    };

    let mut table: [OperandInfo; 32] = [default_operand; 32];

    table[Opcode::LoadConstant as usize] = OperandInfo {
        amount: 1,
        widths: &[2],
    };
    table[Opcode::Add as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::Sub as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::Mul as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::Div as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::Pop as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::True as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::False as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::Equal as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::NotEqual as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::GreaterThan as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::Minus as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::Bang as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::JumpNotTruthy as usize] = OperandInfo {
        amount: 1,
        widths: &[2],
    };
    table[Opcode::Jump as usize] = OperandInfo {
        amount: 1,
        widths: &[2],
    };
    table[Opcode::Null as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::GetGlobal as usize] = OperandInfo {
        amount: 1,
        widths: &[2],
    };
    table[Opcode::SetGlobal as usize] = OperandInfo {
        amount: 1,
        widths: &[2],
    };
    table[Opcode::Array as usize] = OperandInfo {
        amount: 1,
        widths: &[2],
    };
    table[Opcode::Hash as usize] = OperandInfo {
        amount: 1,
        widths: &[2],
    };
    table[Opcode::Index as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::Call as usize] = OperandInfo {
        amount: 1,
        widths: &[1],
    };
    table[Opcode::ReturnValue as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::Return as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::GetLocal as usize] = OperandInfo {
        amount: 1,
        widths: &[1],
    };
    table[Opcode::SetLocal as usize] = OperandInfo {
        amount: 1,
        widths: &[1],
    };
    table[Opcode::GetBuiltin as usize] = OperandInfo {
        amount: 1,
        widths: &[1],
    };
    table[Opcode::Closure as usize] = OperandInfo {
        amount: 3,
        widths: &[2, 1, usize::MAX],
    };
    table[Opcode::GetFree as usize] = OperandInfo {
        amount: 1,
        widths: &[1],
    };
    table[Opcode::CurrentClosure as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::AssignIndexable as usize] = OperandInfo {
        amount: 0,
        widths: &[],
    };
    table[Opcode::AssignFree as usize] = OperandInfo {
        amount: 1,
        widths: &[1],
    };
    table
}

pub static OPERAND_WIDTHS: [OperandInfo; 32] = build_operand_widths();

pub fn make(buffer: &mut Vec<u8>, opcode: Opcode, operands: &[&[u8]]) {
    let expected_amount_operands = OPERAND_WIDTHS[opcode as usize].amount;

    debug_assert_eq!(
        expected_amount_operands,
        operands.len(),
        "opcode {} does not have the correct amount of operands expected {} got {}",
        opcode,
        expected_amount_operands,
        operands.len()
    );

    buffer.push(opcode as u8);

    for (i, operand) in operands.iter().enumerate() {
        let operand_width = OPERAND_WIDTHS[opcode as usize].widths[i];

        if operand_width == usize::MAX {
            buffer.extend_from_slice(operand);
            continue;
        }

        debug_assert_eq!(
            operand_width,
            operand.len(),
            "operand {} for opcode {} does not have the correct width expected {} got {}",
            i,
            opcode,
            operand_width,
            operand.len(),
        );

        buffer.extend_from_slice(operand);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct MakeTestCase<'a> {
        opcode: Opcode,
        operand: &'a [&'a [u8]],
        expected: &'a [u8],
    }

    #[test]
    fn test_make() {
        let tests = [
            MakeTestCase {
                opcode: Opcode::LoadConstant,
                operand: &[&[0xFF, 0xFE]],
                expected: &[0x00, 0xFF, 0xFE],
            },
            MakeTestCase {
                opcode: Opcode::Add,
                operand: &[],
                expected: &[Opcode::Add as u8],
            },
            MakeTestCase {
                opcode: Opcode::GetLocal,
                operand: &[&[0xFF]],
                expected: &[Opcode::GetLocal as u8, 0xFF],
            },
        ];

        for test in tests {
            let mut instruction = Vec::<u8>::new();
            make(&mut instruction, test.opcode, test.operand);

            let instruction_length = instruction.len();
            let expected_length = test.expected.len();
            assert_eq!(
                instruction_length, expected_length,
                "expected instruction length {} got {}",
                expected_length, instruction_length
            );
            assert_eq!(
                test.expected, &instruction,
                "expected instruction {:?} got {:?}",
                test.expected, &instruction
            );
        }
    }
}
