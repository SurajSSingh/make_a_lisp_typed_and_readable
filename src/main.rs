mod step0;
mod step1;

fn main() -> color_eyre::eyre::Result<()> {
    color_eyre::install()?;
    Ok(step1::main()?)
}
