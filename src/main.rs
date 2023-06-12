mod step0_repl;
mod step1_read_print;

fn main() -> color_eyre::eyre::Result<()> {
    color_eyre::install()?;
    Ok(step1_read_print::main()?)
}
