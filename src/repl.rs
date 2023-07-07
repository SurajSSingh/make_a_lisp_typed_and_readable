//! This module holds all functionality for the REPL (Read-Eval-Print-Loop).

use rustyline::{history::History, Editor, Helper, Result};

use crate::{old_repl::MalResult, reader::Form, types::value::MaltarSpannedValue};

pub fn read(line: &str) -> Form<MaltarSpannedValue> {
    todo!()
}

pub fn eval(ast: Form<MaltarSpannedValue>) -> MalResult {
    todo!()
}

pub fn print() {
    todo!()
}

pub fn read_eval_print() {
    todo!()
}

pub fn repl<H, I>(editor: Editor<H, I>) -> Result<()>
where
    H: Helper,
    I: History,
{
    todo!()
}
