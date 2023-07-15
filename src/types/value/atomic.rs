//! This module contains atomic types, which are all types that are self-evaluating
use imstr::ImString;

use fraction::{BigDecimal, DynaDecimal, DynaFraction, DynaInt, GenericDecimal, GenericFraction};
use num::BigInt;
use string_interner::symbol::SymbolUsize;

use super::MaltarTrait;

type X = BigInt;
type Y = GenericDecimal<u64, u16>;
type Z = GenericFraction<u64>;
type W = DynaDecimal<u8, u8>;
type V = DynaFraction<u8>;
type U = DynaInt<GenericFraction<u64>, X>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, derive_more::Display)]
/// A type that represents itself. These can be constructed from literals.
pub enum AtomicValue {
    #[display(fmt = "nil")]
    /// A nil value representing nothing
    Nil(()),
    /// A boolean value
    Bool(bool),
    /// A generic number type that behaves like an integer, rational, or floating point number.
    Number(GenericDecimal<u64, u16>),
    /// An immutable string
    String(ImString),
    /// Symbol that evaluates to itself. Is interned like a symbol.
    #[display(fmt = "keyword:{_0:?}")]
    Keyword(SymbolUsize),
}

fn print_fraction(x: GenericDecimal<u64, u16>) -> fraction::GenericFraction<u64> {
    let mut s = GenericFraction::NaN;
    x.map_ref(|x| {
        s = *x;
        *x
    });
    s
}

impl MaltarTrait for AtomicValue {}

#[cfg(test)]
mod tests {
    use crate::types::value::atomic::AtomicValue;

    #[test]
    fn test_number() {
        let x = AtomicValue::Number((1).into());
        let y = AtomicValue::Number((7).into());
        eprintln!("Number {}", AtomicValue::Number((0).into()));
        eprintln!("Number {}", AtomicValue::Number((7).into()));
        eprintln!("Number {}", AtomicValue::Number((-7).into()));
        eprintln!("Number {}", AtomicValue::Number((0.24).into()));
        if let AtomicValue::Number(xi) = x {
            if let AtomicValue::Number(yi) = y {
                crate::types::value::atomic::print_fraction(xi / yi);
                // eprintln!("{} / {} == {}", xi, yi, print_fraction(xi / yi));
            }
        }
    }
}
