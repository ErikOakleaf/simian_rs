mod backend;
mod frontend;
mod runtime;
mod repl;

fn main() -> Result<(), String> {
    repl::start()?;
    Ok(())
}
