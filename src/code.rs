use std::alloc::{alloc, Layout};

#[repr(u8)]
pub enum Opcode {
    OpConstant = 0x00,
}

const fn build_operand_widths() -> [u8; 256] {
    let mut table = [0u8; 256];
    table[Opcode::OpConstant as usize] = 2;
    table
}

static OPERAND_WIDTHS: [u8; 256] = build_operand_widths();

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

    #[test]
    fn test_make() {
        let tests = [(Opcode::OpConstant, &[0xFF, 0xFE], [0x00, 0xFF, 0xFE])];

        for (opcode, operands, expected) in tests {
            let instruction = make(opcode, operands);

            let instruction_length = instruction.len();
            let expected_length = expected.len();
            assert_eq!(
                instruction_length, expected_length,
                "expected instruction length {} got {}",
                expected_length, instruction_length
            );
            assert_eq!(
                instruction.as_ref(),
                expected,
                "expected instruction {:?} got {:?}",
                expected,
                instruction
            );
        }
    }
}
