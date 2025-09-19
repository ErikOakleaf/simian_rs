pub mod evaluator;
pub mod object;
pub mod vm;

pub use evaluator::eval_program;
pub use object::Object;
pub use vm::VM;
