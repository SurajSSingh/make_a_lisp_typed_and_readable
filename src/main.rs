use std::error::Error;

mod step0_repl;
mod step1_read_print;
mod step2_eval;
mod step3_env;
mod step4_if_fn_do;
mod step5_tco;
mod step6_file;
fn main() -> Result<(), Box<dyn Error>> {
    Ok(step6_file::main()?)
}
