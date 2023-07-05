// WIP: #2
// use std::ops::Add;

// use fraction::{DynaDecimal, DynaFraction, DynaInt, GenericDecimal, GenericFraction};

// #[derive(
//     Debug, Clone, PartialEq, Eq, PartialOrd, Ord, derive_more::From, derive_more::Into, Hash,
// )]
// /// TODO: Make actual big decimal
// ///
// /// Idea: 1st number represents scale, 2nd is signed int, rest is the number as BigUint
// struct BigDecimal(fraction::BigUint);

// impl std::fmt::Display for BigDecimal {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         todo!()
//     }
// }

// #[derive(
//     Debug,
//     Clone,
//     PartialEq,
//     Eq,
//     PartialOrd,
//     Ord,
//     derive_more::From,
//     derive_more::TryInto,
//     derive_more::Display,
// )]
// pub enum NumericType {
//     Integer(DynaInt<i64, fraction::BigInt>),
//     Rational(GenericFraction<u64>),
//     Float(GenericDecimal<u32, u16>),
//     BigDecimal(BigDecimal),
// }

// impl std::hash::Hash for NumericType {
//     fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
//         // core::mem::discriminant(self).hash(state);
//         todo!()
//     }
// }

// WIP: #1

// use std::{cmp::Ordering, ops::Neg};

// use num::{rational::Ratio, BigInt, Signed, ToPrimitive, Zero};
// use ordered_float::FloatIsNan;
// use std::ops::{Add, Div, Mul, Range, Sub};

// use ordered_float::OrderedFloat;

// use crate::types::error::{ArithmaticOperator, NumericError};

// #[derive(Debug, Eq, Clone, Copy, derive_more::From, derive_more::TryInto, derive_more::Display)]
// /// Represents any numeric type (e.g. natural, integers, reals, complex, etc.).
// /// There are some overlap between these types.
// ///
// /// Upcast allowed (i.e. integer promotes to rational or float, and rational promote to float).
// ///
// /// NOTE: BigInt and BigDecimal are not supported as a built-in type, but they may be supported as library types.
// pub enum NumericType {
//     /// Integer numerals
//     ///
//     /// Construct over these Rust types: i8, u8, i16, u16, i32, u32, i64
//     #[from(types(i8, u8, i16, u16, i32, u32))]
//     Integer(i64),
//     BigInt(BigInt),
//     /// Rational numerals: sign u32/u32
//     #[display(fmt = "{}{}", _0, _1)]
//     Rational(Sign, Ratio<u32>),
//     /// Any non-NAN floating point number
//     ///
//     /// Construct over these Rust types: f32, f64
//     ///
//     /// Note: Should assume behavior of NonNan, with panics replaced with returning Error
//     Float(OrderedFloat<f64>),
// }

// impl Add for NumericType {}

// impl NumericType {
//     /// Try to reduce a [NumericType] to [NumericType::Integer] when possible.
//     pub fn reduced_form(&self) -> Self {
//         match self {
//             // Integer is the lowest numeric form - no change
//             integer @ NumericType::Integer(_) => *integer,
//             // If rational is an integer, make it an integer, or return as is
//             rational @ NumericType::Rational(s, q) => {
//                 if q.is_integer() {
//                     NumericType::Integer(as_i64(s, q.numer()))
//                 } else {
//                     *rational
//                 }
//             }
//             //
//             float @ NumericType::Float(OrderedFloat(f)) => {
//                 if f.is_finite() {
//                     // If f has no fractional part, try to make into integer or keep as is
//                     if f.trunc() == *f {
//                         f.to_i64().map(NumericType::Integer).unwrap_or(*float)
//                     } else {
//                         // Make ratio from larger range becuase u32 is not signed
//                         Ratio::<i64>::approximate_float(*f)
//                             // Convert to (sign, u32 ratio)
//                             .and_then(|r_big| {
//                                 match (r_big.numer().to_u32(), r_big.denom().to_u32()) {
//                                     (Some(n), Some(d)) if d != 0 => {
//                                         Some((r_big.is_negative(), Ratio::new_raw(n, d)))
//                                     }
//                                     _ => None,
//                                 }
//                             })
//                             .map(|(s, r)| NumericType::Rational(Sign::true_as_minus(s), r))
//                             // If None at any point, just leave alone
//                             .unwrap_or(*float)
//                     }
//                 } else {
//                     *float
//                 }
//             }
//         }
//     }
// }

// macro_rules! impl_float_to_real {
//     ($($float:ty),+) => {
//         $(impl TryFrom<$float> for NumericType {
//             type Error = FloatIsNan;

//             fn try_from(value: $float) -> Result<Self, Self::Error> {
//                 if value.is_nan() {
//                     Err(FloatIsNan)
//                 } else {
//                     Ok(NumericType::Float(OrderedFloat(value.into())))
//                 }
//             }
//         })+
//     };
// }

// impl_float_to_real!(f32, f64);

// impl Default for NumericType {
//     fn default() -> Self {
//         NumericType::Integer(i64::default())
//     }
// }

// impl Neg for NumericType {
//     type Output = Self;

//     fn neg(self) -> Self::Output {
//         match self {
//             NumericType::Integer(i) => NumericType::Integer(-i),
//             NumericType::Rational(s, q) => NumericType::Rational(-s, q),
//             NumericType::Float(f) => NumericType::Float(-f),
//         }
//     }
// }

// impl PartialEq for NumericType {
//     fn eq(&self, other: &Self) -> bool {
//         match (self, other) {
//             // Same Type
//             (NumericType::Integer(l0), NumericType::Integer(r0)) => l0 == r0,
//             (NumericType::Rational(l0, l1), NumericType::Rational(r0, r1)) => l0 == r0 && l1 == r1,
//             (NumericType::Float(l0), NumericType::Float(r0)) => l0 == r0,
//             // Different types
//             (NumericType::Integer(i), NumericType::Rational(s, q))
//             | (NumericType::Rational(s, q), NumericType::Integer(i)) => {
//                 q.is_integer() && ((q.is_zero() && i.is_zero()) || *i == as_i64(s, q.numer()))
//             }
//             (NumericType::Integer(i), NumericType::Float(f))
//             | (NumericType::Float(f), NumericType::Integer(i)) => *i as f64 == f.0,

//             (NumericType::Rational(s, q), NumericType::Float(f))
//             | (NumericType::Float(f), NumericType::Rational(s, q)) => {
//                 as_f64(s, q).map(|qf| qf == f.0).unwrap_or(false)
//             }
//         }
//     }
// }

// impl PartialOrd for NumericType {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         Some(match (self, other) {
//             (NumericType::Integer(i0), NumericType::Integer(i1)) => i0.cmp(i1),
//             (NumericType::Rational(s0, q0), NumericType::Rational(s1, q1)) => {
//                 // Both zero regardless of sign
//                 if q0.is_zero() && q1.is_zero() {
//                     Ordering::Equal
//                 } else {
//                     // Negative < Positive, if same sign, cmp ratios
//                     match s0.cmp(s1) {
//                         Ordering::Equal => q0.cmp(q1),
//                         ordering => ordering,
//                     }
//                 }
//             }
//             (NumericType::Float(r0), NumericType::Float(r1)) => r0.cmp(r1),
//             (NumericType::Integer(i0), NumericType::Rational(s1, q1)) => todo!(),
//             (NumericType::Integer(i0), NumericType::Float(_)) => todo!(),
//             (NumericType::Rational(_, _), NumericType::Integer(i1)) => todo!(),
//             (NumericType::Rational(_, _), NumericType::Float(_)) => todo!(),
//             (NumericType::Float(_), NumericType::Integer(i1)) => todo!(),
//             (NumericType::Float(_), NumericType::Rational(_, _)) => todo!(),
//         })
//     }
// }

// impl Ord for NumericType {
//     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//         self.partial_cmp(other)
//             .expect("Partial compare should return exact ordering")
//     }
// }

// impl Add<NumericType> for NumericType {
//     type Output = Result<NumericType, NumericError>;

//     /// Add two numeric types with the following properties:
//     /// 1. Type promotions (symmetric across operator):
//     ///     1. Float + any = Float
//     ///     2. Rational + Integer = Rational
//     ///     3. Integer + Integer = Integer
//     /// 2. Overflow means giving back positive INFINITY
//     fn add(self, rhs: NumericType) -> Self::Output {
//         match (self, rhs) {
//             // Same subtypes
//             (NumericType::Integer(i0), NumericType::Integer(i1)) => match i0.overflowing_add(i1) {
//                 (res, false) => Ok(NumericType::Integer(res)),
//                 // Integer overflow becomes infinite
//                 // TODO: is that reasonable?
//                 (_, true) => Ok(NumericType::Float(OrderedFloat(f64::INFINITY))),
//             },
//             (NumericType::Rational(s0, q0), NumericType::Rational(s1, q1)) => todo!(),
//             (NumericType::Float(f0), NumericType::Float(f1)) => Ok(NumericType::Float(f0 + f1)),
//             // Different subtypes
//             (NumericType::Integer(i), NumericType::Rational(s, q))
//             | (NumericType::Rational(s, q), NumericType::Integer(i)) => {
//                 // If rational is an integer, add as integer
//                 if q.is_integer() {
//                     match i.overflowing_add(as_i64(&s, q.numer())) {
//                         (res, false) => Ok(NumericType::Integer(res)),
//                         // Integer overflow becomes infinite
//                         // TODO: is that reasonable?
//                         (_, true) => Ok(NumericType::Float(OrderedFloat(f64::INFINITY))),
//                     }
//                 } else {
//                     // Otherwise, add as rational value:
//                     // n = numerator with sign, d = denominator, i = integer
//                     // (1) n/d + i/1
//                     let n = as_i64(&s, q.numer());
//                     let d = *q.denom() as i64;
//                     // (2) n/d + (i*d)/d
//                     let i_times_d = match i.overflowing_mul(d){
//                         (res, false) => res,
//                         (_ true) =>
//                     };
//                     // (3) (n + i*d)/d
//                     match n.overflowing_add(i_times_d){
//                         (res, false) => todo!(),
//                         (_, true) =>
//                     }
//                     let new_n = ;
//                     let new_rational = Ratio<>

//                 }
//             }
//             (NumericType::Integer(i), NumericType::Float(f))
//             | (NumericType::Float(f), NumericType::Integer(i)) => {
//                 Ok(NumericType::Float(f + i as f64))
//             }
//             (num1 @ NumericType::Rational(s, q), num2 @ NumericType::Float(f))
//             | (num1 @ NumericType::Float(f), num2 @ NumericType::Rational(s, q)) => {
//                 match as_f64(&s, &q).map(|qf| qf + f.0) {
//                     Some(res) if res.is_nan() => Err(NumericError::FloatIsNan),
//                     Some(res) => Ok(NumericType::Float(OrderedFloat(res))),
//                     None => Err(NumericError::CalculationFailure(
//                         ArithmaticOperator::Add,
//                         num1,
//                         num2,
//                     )),
//                 }
//             }
//         }
//     }
// }

// impl std::hash::Hash for NumericType {
//     fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
//         // core::mem::discriminant(self).hash(state);
//         // Idea: check for lowest type before hashing
//         todo!()
//     }
// }

// #[cfg(test)]
// mod tests {}
// #[derive(
//     PartialEq, PartialOrd, Eq, Ord, Copy, Clone, Debug, Hash, derive_more::Display, Default,
// )]
// /// Represents either a negative or a positive sign, defaults to positive
// pub enum Sign {
//     #[display(fmt = "-")]
//     /// Negative, represented by minus sign (-)
//     Minus,
//     #[default]
//     #[display(fmt = "+")]
//     /// Positive, represented by plus sign (+)
//     Plus,
// }

// impl Sign {
//     /// Convert a sign to either +1 for [Sign::Plus] or -1 for [Sign::Minus]
//     pub fn as_num(&self) -> i8 {
//         match self {
//             Sign::Minus => -1,
//             Sign::Plus => 1,
//         }
//     }

//     /// Returns [Sign::Minus] when true, otherwise [Sign::Plus].
//     pub fn true_as_minus(neg_sign: bool) -> Sign {
//         if neg_sign {
//             Self::Minus
//         } else {
//             Self::Plus
//         }
//     }

//     /// Returns [Sign::Plus] when true, otherwise [Sign::Minus].
//     pub fn true_as_plus(pos_sign: bool) -> Sign {
//         Sign::true_as_minus(!pos_sign)
//     }

//     /// Returns [Sign::Minus] when negative, otherwise [Sign::Plus] (0 or positive).
//     pub fn from_num(num: i64) -> Sign {
//         if num.is_negative() {
//             Self::Minus
//         } else {
//             Self::Plus
//         }
//     }

//     /// Returns `true` if the sign is [`Minus`].
//     ///
//     /// [`Minus`]: Sign::Minus
//     #[must_use]
//     pub fn is_minus(&self) -> bool {
//         matches!(self, Self::Minus)
//     }

//     /// Returns `true` if the sign is [`Plus`].
//     ///
//     /// [`Plus`]: Sign::Plus
//     #[must_use]
//     pub fn is_plus(&self) -> bool {
//         matches!(self, Self::Plus)
//     }
// }

// impl Neg for Sign {
//     type Output = Self;

//     fn neg(self) -> Self::Output {
//         match self {
//             Sign::Minus => Sign::Plus,
//             Sign::Plus => Sign::Minus,
//         }
//     }
// }

// /// Given a [Sign] and a [u32] value, returns it as an [i64].
// fn as_i64(sign: &Sign, value: &u32) -> i64 {
//     *value as i64 * sign.as_num() as i64
// }

// /// Given a [Sign] and a [Ratio] of [u32] value, returns an [f64].
// fn as_f64(sign: &Sign, value: &Ratio<u32>) -> Option<f64> {
//     value.to_f64().map(|f| f * sign.as_num() as f64)
// }
