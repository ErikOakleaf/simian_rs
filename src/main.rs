mod token;
mod lexer;
mod repl;
mod ast;
mod parser;
mod object;
mod evaluator;

fn main() -> Result<(), String>{
    repl::start()?;
    Ok(())
}
