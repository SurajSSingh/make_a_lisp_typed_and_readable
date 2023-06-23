use std::error::Error;

mod mal_steps;
fn main() -> Result<(), Box<dyn Error>> {
    Ok(mal_steps::stepA_mal::main()?)
}
