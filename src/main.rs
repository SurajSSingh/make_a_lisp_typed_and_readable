mod step0_repl;
mod step1_read_print;
mod step2_eval;
mod step3_env;
mod step4_if_fn_do;
mod step5_tco;
fn main() -> color_eyre::eyre::Result<()> {
    color_eyre::install()?;
    Ok(step5_tco::main()?)
}
