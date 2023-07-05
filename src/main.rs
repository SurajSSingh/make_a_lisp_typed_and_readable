//! This is an implemtation of [MAL](https://github.com/kanaka/mal/), a simple lisp dialect inspired by Clojure
#![deny(missing_docs)]
use std::error::Error;

use old_reader::MalType;
use old_repl::{repl, ReplError};

mod old_core;
mod old_env;
mod old_printer;
mod old_reader;
mod old_repl;

fn main() -> Result<(), Box<dyn Error>> {
    Ok(repl()?)
}
