//! This module contains all items related to the REPL

use crate::types::error::ProgramResult;

// /// Read in a string and parse it into an AST expression
// fn read(line: String) -> ProgramResult<String> {
//     let expr = *reader::read_str(&line).map_err()?;
//     Ok(expr)
// }

// pub fn read_eval(line: String, env: &NewEnv) {
//     let ast = read(line)?;
//     let res = eval(ast, env.clone())?;
// }

pub fn default_repl() {}
