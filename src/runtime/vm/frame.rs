use crate::runtime::Object;

pub struct Frame {
    pub function: Box<[u8]>,
    pub ip: usize,
}

impl Frame {
    pub fn new(function: Box<[u8]>) -> Self {
       Frame { function: function, ip: 0 }  
    }
}
