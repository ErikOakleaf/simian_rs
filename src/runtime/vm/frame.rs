use crate::runtime::Object;

pub struct Frame {
    pub function: Box<[u8]>,
    pub ip: usize,
    pub base_pointer: usize,
}

impl Frame {
    pub fn new(function: Box<[u8]>, base_pointer: usize) -> Self {
       Frame { function: function, ip: 0, base_pointer: base_pointer }  
    }
}
