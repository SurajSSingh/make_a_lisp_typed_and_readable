//! This module contains all types related to errors

#[derive(Debug, Clone, PartialEq, derive_more::Display)]
pub enum LexError {}

#[derive(Debug, Clone, PartialEq, derive_more::Display)]
pub enum ParseError {}

#[derive(Debug, Clone, PartialEq, derive_more::Display)]
pub enum TypeError {}

#[derive(Debug, Clone, PartialEq, derive_more::Display)]
pub enum EvalError {}

#[derive(Debug, Clone, PartialEq, derive_more::Display)]
pub enum Error {
    Lex(LexError),
    Parse(ParseError),
    Type(TypeError),
    Eval(EvalError),
}
