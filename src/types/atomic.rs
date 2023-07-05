//! This file contains types whose values are self evaluated.
//! All of them can be constructed from literals during the lexing process and hold onto exactly one type of value.

use imstr::ImString;

use string_interner::symbol::SymbolUsize;

use crate::reader::lexer::NewToken;

pub mod numeric;

#[derive(
    Debug,
    PartialOrd,
    Ord,
    PartialEq,
    Eq,
    Clone,
    Hash,
    derive_more::From,
    derive_more::TryInto,
    derive_more::Display,
)]
/// Atomic values, these are singular value, self-evaluating, and can be used for hash-map keys
pub enum AtomicType {
    /// A versatile empty type representing:
    /// * Falsy (boolean)
    /// * Empty Collection
    #[display(fmt = "nil")]
    Nil(()),
    /// Boolean value (either true or false)
    Bool(bool),
    /// Single UTF-8 character
    Char(char),
    #[display(fmt = "keyword:{:#?}", _0)]
    /// A keyword, like a symbol that starts with ":", evaluates to itself
    Keyword(SymbolUsize),
    /// A number, can be any of integer, rational, or float
    // TODO: Replace with numeric type enum once that is completed
    Number(fraction::GenericDecimal<u64, u16>),
    /// An immutable string
    String(ImString),
}

impl Default for AtomicType {
    fn default() -> Self {
        AtomicType::Nil(())
    }
}

impl TryFrom<NewToken> for AtomicType {
    type Error = NewToken;

    fn try_from(value: NewToken) -> Result<Self, Self::Error> {
        todo!()
    }
}
