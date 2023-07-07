//! This module contains all types related to errors

#[derive(Debug, Clone, PartialEq, Default, derive_more::Display)]
pub enum LexError {
    #[default]
    Default,
}
pub type LexResult<T> = Result<T, LexError>;

#[derive(Debug, Clone, PartialEq, derive_more::Display)]
pub enum ParseError {}

#[derive(Debug, Clone, PartialEq, derive_more::Display)]
pub enum TypeError {}

#[derive(Debug, Clone, PartialEq, derive_more::Display)]
pub enum EvalError {}

#[derive(
    Debug, Clone, PartialEq, derive_more::Display, derive_more::From, derive_more::TryInto,
)]
pub enum Error {
    Lex(LexError),
    Parse(ParseError),
    Type(TypeError),
    Eval(EvalError),
    Custom(String),
}
