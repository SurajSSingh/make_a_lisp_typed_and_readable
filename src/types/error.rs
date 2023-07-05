//! These are types that are used to represent errors at different stages of the program

use std::ops::Range;

use super::DataType;

pub type LexResult<T> = Result<T, LexError>;
pub type ParseResult<T> = Result<T, ParseError>;
pub type EvalResult<T> = Result<T, EvalError>;
pub type ProgramResult<T> = Result<T, ErrorType>;

#[derive(Debug, Clone, PartialEq, Default)]
/// Errors that occur during the lexing process
pub enum LexError {
    #[default]
    Default,
    NumberParse(String),
    InvalidCharacter(String),
}

#[derive(Debug, Clone, PartialEq)]
/// Errors that occur during the parsing stage
pub enum ParseError {
    /// Missing an ending character, show what it expects there to be
    UnbalancedParen(&'static str),
}

#[derive(Debug, Clone, PartialEq)]
/// Errors that occur during the type checking stage
pub enum TypeError {}

#[derive(Debug, Clone, PartialEq)]
/// Errors that occur during the evaluation stage
pub enum EvalError {
    /// Function received not enough arguments to run
    NotEnoughArguments { expect: Range<u8>, got: u8 },
}

#[derive(Debug, Clone, PartialEq, Default, derive_more::From)]
/// Union of all the types of errors in the program
pub enum ErrorType {
    #[default]
    /// Unknown Error: ***ONLY USE FOR TEMPORARY ERRORS***
    Unknown,
    /// Error in Lexing
    Lex(LexError),
    /// Error in Parsing
    Parse(ParseError),
    /// Error in type inference/checking
    Type(TypeError),
    /// Error in Evaluation
    Eval(EvalError),
    /// Runtime Exception
    Exception(DataType),
    Custom(String),
}

impl ErrorType {}
