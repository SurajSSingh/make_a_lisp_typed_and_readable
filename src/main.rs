use rustyline::{error::ReadlineError, DefaultEditor, Result};

fn read(rl: &mut DefaultEditor) -> Result<String> {
    let line = rl.readline("user> ")?;
    rl.add_history_entry(line.clone())?;
    Ok(line)
}

fn eval(ast: String) -> String {
    ast
}

fn print(value: String) {
    println!("{value}")
}

fn rep(rl: &mut DefaultEditor) -> Result<()> {
    print(eval(read(rl)?));
    Ok(())
}

fn main() -> Result<()> {
    let mut rl = DefaultEditor::new()?;
    loop {
        if let Err(err) = rep(&mut rl) {
            match err {
                ReadlineError::Eof | ReadlineError::Interrupted => break,
                _ => {
                    println!("{}", err);
                    break;
                }
            }
        }
    }
    Ok(())
}
