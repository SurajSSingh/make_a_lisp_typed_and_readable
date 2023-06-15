mod step0_repl;
mod step1_read_print;
mod step2_eval;
mod step3_env;

fn main() -> color_eyre::eyre::Result<()> {
    color_eyre::install()?;
    Ok(step3_env::main()?)
}
