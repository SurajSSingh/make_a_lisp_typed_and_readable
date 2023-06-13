mod step0_repl;
mod step1_read_print;
mod step2_eval;

fn main() -> color_eyre::eyre::Result<()> {
    color_eyre::install()?;
    Ok(step2_eval::main()?)
}
