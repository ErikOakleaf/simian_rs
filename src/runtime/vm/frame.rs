use std::rc::Rc;

use crate::runtime::object::Closure;

pub struct Frame {
    pub closure: Rc<Closure>,
    pub ip: usize,
    pub base_pointer: usize,
}

impl Frame {
    pub fn new(closure: Rc<Closure>, base_pointer: usize) -> Self {
        Frame {
            closure: closure,
            ip: 0,
            base_pointer: base_pointer,
        }
    }

    pub fn instructions(&self) -> &[u8] {
        &self.closure.function.instructions
    }
}
