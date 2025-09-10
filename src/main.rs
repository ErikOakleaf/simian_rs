mod token;
mod lexer;
mod repl;
mod ast;
mod parser;
mod object;
mod evaluator;
mod code;
mod compiler;
mod vm;

fn main() -> Result<(), String>{
    repl::start()?;
    Ok(())
}
