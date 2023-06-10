use rustyline::{error::ReadlineError, DefaultEditor, Result};

fn read(line: String) -> String {
    todo!()
}

fn eval(ast: String) -> String {
    todo!()
}

fn print(value: String) {
    println!("{value}")
}

fn rep(input: String) {
    print(input)
}

fn main() -> Result<()> {
    let mut rl = DefaultEditor::new()?;
    loop {
        let readline = rl.readline("user> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.clone())?;
                rep(line)
            }
            Err(ReadlineError::Eof | ReadlineError::Interrupted) => break,
            Err(err) => {
                println!("{}", err);
                break;
            }
        }
    }
    Ok(())
}
