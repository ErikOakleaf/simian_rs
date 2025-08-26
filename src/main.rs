use crate::parser::ParseError;

mod token;
mod lexer;
mod repl;
mod ast;
mod parser;

fn main() -> Result<(), ParseError>{
    repl::start()?;
    Ok(())
}
