use imstr::ImString;

use string_interner::symbol::SymbolUsize;

use crate::reader::lexer::{LexError, NewToken};

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
/// Atomic values, these are self-evaluating and can be used for hash-map keys
pub enum AtomicType {
    /// A versatile empty type representing:
    /// * Falsy (boolean)
    /// * NULL char (character)
    /// * Nan (number)
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
    /// A number, either integer, rational, or float
    Number(numeric::NumericType),
    /// An immutable string
    String(ImString),
}

impl Default for AtomicType {
    fn default() -> Self {
        AtomicType::Nil(())
    }
}

impl TryFrom<NewToken> for AtomicType {
    type Error = LexError;

    fn try_from(value: NewToken) -> Result<Self, Self::Error> {
        todo!()
    }
}
