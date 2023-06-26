use std::ops::{Add, Div, Mul, Neg, Range, Sub};

use im::{HashMap, HashSet, Vector};
use imstr::ImString;
use logos::Span;
use num_rational::Ratio;
use ordered_float::{FloatIsNan, OrderedFloat};
use string_interner::symbol::SymbolUsize;

use crate::new_env::EnvStruct;

pub type DataValueResult = Result<DataValue, ErrorType>;

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

// impl<T> Add<Result<DataType<T>, ErrorType>> for NumericType where T: Clone + PartialEq + Eq + std::hash::Hash {
//     type Output = Result<DataType<T>, ErrorType>;

//     fn add(self, rhs: Result<DataType<T>, ErrorType>) -> Self::Output {
//         match rhs
//     }
// }

#[derive(
    Debug,
    PartialOrd,
    Ord,
    PartialEq,
    Eq,
    Clone,
    Hash,
    Default,
    derive_more::From,
    derive_more::TryInto,
    derive_more::Display,
)]
/// Atomic values, these are self-evaluating and can be used for hash-map keys
pub enum AtomicType {
    #[default]
    /// A versatile empty type representing:
    /// * Falsy (boolean)
    /// * NULL char (character)
    /// * Nan (number)
    /// * Empty Collection
    Nil,
    /// Boolean value (either true or false)
    Bool(bool),
    /// Single UTF-8 character
    Char(char),
    #[display(fmt = "keyword:{:#?}", _0)]
    /// A keyword, like a symbol that starts with ":", evaluates to itself
    Keyword(SymbolUsize),
    /// A number, either integer, rational, or float
    Number(NumericType),
    /// An immutable string
    String(ImString),
}

// macro_rules! impl_atomic_from {
//     ($($from_type:ty),+ => $result_type:ident) => {
//         $(impl From<$from_type> for AtomicType
//         {
//             fn from(_value: $from_type) -> Self {
//                 AtomicType::$result_type
//             }
//         })+
//     };
//     ($($from_type:ty),+ => $result_type:ident()) => {
//         $(impl From<$from_type> for AtomicType
//         {
//             fn from(value: $from_type) -> Self {
//                 AtomicType::$result_type(value.into())
//             }
//         })+
//     };
// }

// impl_atomic_from!(() => Nil);
// impl_atomic_from!(bool => Bool());
// impl_atomic_from!(char => Char());
// impl_atomic_from!(&str, String  => String());
// // impl_atomic_from!(&str, String  => Number());

#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Hash,
    Default,
    derive_more::From,
    derive_more::Into,
    derive_more::Display,
)]
#[display(fmt = "{}@{:#?}", value, span)]
/// Atomic type that has span information
pub struct SpannedAtomic {
    value: AtomicType,
    span: Span,
}

#[derive(Debug, Clone, derive_more::From, derive_more::TryInto, derive_more::Display)]
pub enum FunctionType<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    #[display(fmt = "Built-in: {}({:#?})", name, arity)]
    LiftedFunction {
        name: &'static str,
        arity: Range<u8>,
        func: fn(Vector<Val>) -> DataValueResult,
    },
    #[display(fmt = "({} {:?} {})", "self.get_name()", params, ast)]
    UserDefinedFunction {
        name: Option<ImString>,
        ast: Box<Val>,
        params: Vector<ImString>,
        env: EnvStruct,
        val: Box<Val>,
    },
}

impl<Val> PartialEq for FunctionType<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::LiftedFunction {
                    name: l_name,
                    arity: l_arity,
                    func: l_func,
                },
                Self::LiftedFunction {
                    name: r_name,
                    arity: r_arity,
                    func: r_func,
                },
            ) => l_name == r_name && l_arity == r_arity && l_func == r_func,
            (
                Self::UserDefinedFunction {
                    name: l_name,
                    ast: l_ast,
                    params: l_params,
                    env: _l_env,
                    val: l_val,
                },
                Self::UserDefinedFunction {
                    name: r_name,
                    ast: r_ast,
                    params: r_params,
                    env: _r_env,
                    val: r_val,
                },
            ) => l_name == r_name && l_ast == r_ast && l_params == r_params && l_val == r_val,
            _ => false,
        }
    }
}

impl<Val> FunctionType<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    pub fn get_name(&self) -> String {
        match self {
            FunctionType::LiftedFunction { name, .. } => name.to_string(),
            FunctionType::UserDefinedFunction { name, .. } => name
                .clone()
                .map(|s| s.into_std_string())
                .unwrap_or(String::from("fn")),
        }
    }
}

#[derive(
    Debug, Clone, PartialEq, derive_more::From, derive_more::TryInto, derive_more::Display,
)]
/// The data types represented by the program
pub enum DataType<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    Atomic(AtomicType),
    #[display(fmt = "symbol_{:#?}", _0)]
    Symbol(SymbolUsize),
    List(Vector<Val>),
    #[from(ignore)]
    Vector(Vector<Val>),
    HashMap(HashMap<AtomicType, Val>),
    HashSet(HashSet<Val>),
    Function(FunctionType<Val>),
}

impl<Val: std::hash::Hash> std::hash::Hash for DataType<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
    }
}

impl<Val: Eq> Eq for DataType<Val> where Val: Clone + PartialEq + Eq + std::hash::Hash {}

impl<Val> Default for DataType<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    fn default() -> Self {
        DataType::Atomic(AtomicType::default())
    }
}

impl<Val> From<Option<DataType<Val>>> for DataType<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    fn from(value: Option<DataType<Val>>) -> Self {
        value.unwrap_or_default()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Instances a data type recursively
pub struct DataValue(pub DataType<DataValue>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Spanned representation of Data values
pub struct SpannedValue {
    pub value: DataType<SpannedValue>,
    pub meta: DataValue,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    /// Missing an ending character, show what it expects there to be
    UnbalancedParen(&'static str),
}

#[derive(Debug, Clone, PartialEq)]
pub enum EvalError {
    NotEnoughArguments { expect: Range<u8>, got: u8 },
}

#[derive(Debug, Clone, PartialEq, Default)]
/// Union of all the types of errors in the program
pub enum ErrorType {
    /// Error in Parsing
    Parse(ParseError),
    /// Error in Evaluation
    Eval(EvalError),
    /// Runtime Exception
    Exception(DataValue),
    #[default]
    /// Unknown Error: ***ONLY USE FOR TEMPORARY ERRORS***
    Unknown,
}

impl ErrorType {}
