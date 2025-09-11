use std::env;

mod ast;
mod code;
mod compiler;
mod evaluator;
mod lexer;
mod object;
mod parser;
mod repl;
mod token;
mod vm;

fn main() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();

    let mode = if args.len() > 1 {
        match args[1].as_str() {
            "interpreter" => 0,
            "vm" => 1,
            other => return Err(format!("Unknown mode: {}", other)),
        }
    } else {
        return Err("No mode provided. Use 'vm' or 'interpreter'.".to_string());
    };

    repl::start(mode)?;
    Ok(())
}
