use crate::parser::ParseError;

mod token;
mod lexer;
mod repl;
mod ast;
mod parser;
mod object;

fn main() -> Result<(), ParseError>{
    repl::start()?;
    Ok(())
}
