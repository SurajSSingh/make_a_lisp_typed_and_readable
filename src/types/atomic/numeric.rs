use std::ops::Neg;

use num_rational::Ratio;
use ordered_float::FloatIsNan;
use std::ops::{Add, Div, Mul, Range, Sub};

use ordered_float::OrderedFloat;

#[derive(Debug, Eq, Clone, Copy, derive_more::From, derive_more::TryInto, derive_more::Display)]
#[non_exhaustive]
/// Represents any numeric type (e.g. natural, integers, reals, complex, etc.).
/// There are some overlap between these types.
pub enum NumericType {
    /// Integer numerals
    ///
    /// Construct over these Rust types: i8, u8, i16, u16, i32, u32, i64
    #[from(types(i8, u8, i16, u16, i32, u32))]
    Integer(i64),
    /// Rational numerals: signed u32/u32
    #[display(fmt = "{}{}", "to_sign(_0)", _1)]
    Rational(bool, Ratio<u32>),
    /// Any non-NAN floating point number
    ///
    /// Construct over these Rust types: f32, f64
    ///
    /// Note: Should assume behavior of NonNan, with panics replaced with returning Error
    Real(OrderedFloat<f64>),
}

pub fn to_sign(b: &bool) -> &'static str {
    if *b {
        "-"
    } else {
        "+"
    }
}

impl PartialEq for NumericType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            // Same Type
            (Self::Integer(l0), Self::Integer(r0)) => l0 == r0,
            (Self::Rational(l0, l1), Self::Rational(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::Real(l0), Self::Real(r0)) => l0 == r0,
            // Different types
            _ => false,
        }
    }
}

impl Ord for NumericType {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap_or(std::cmp::Ordering::Equal)
    }
}

impl PartialOrd for NumericType {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        todo!()
    }
}

impl std::hash::Hash for NumericType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
    }
}

macro_rules! impl_float_to_real {
    ($($float:ty),+) => {
        $(impl TryFrom<$float> for NumericType {
            type Error = FloatIsNan;

            fn try_from(value: $float) -> Result<Self, Self::Error> {
                if value.is_nan() {
                    Err(FloatIsNan)
                } else {
                    Ok(NumericType::Real(OrderedFloat(value.into())))
                }
            }
        })+
    };
}

impl_float_to_real!(f32, f64);

impl Default for NumericType {
    fn default() -> Self {
        NumericType::Integer(i64::default())
    }
}

impl Neg for NumericType {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            NumericType::Integer(i) => NumericType::Integer(-i),
            NumericType::Rational(s, q) => NumericType::Rational(!s, q),
            NumericType::Real(f) => NumericType::Real(-f),
        }
    }
}
