use std::ops::Add;

use kstring::KString;

use imstr::ImString;

use fraction::{DynaDecimal, GenericDecimal, GenericFraction};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, derive_more::Display)]
pub enum AtomicValue {
    #[display(fmt = "nil")]
    Nil(()),
    Bool(bool),

    Float(GenericDecimal<u64, u16>),
    String(ImString),
    Keyword(KString),
}
