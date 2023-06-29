pub mod atomic;

use std::ops::Range;

use im::{HashMap, HashSet, Vector};
use imstr::ImString;
use logos::Span;
use string_interner::symbol::SymbolUsize;

use crate::new_env::EnvStruct;

pub type DataValueResult = Result<DataValue, ErrorType>;

// impl<T> Add<Result<DataType<T>, ErrorType>> for NumericType where T: Clone + PartialEq + Eq + std::hash::Hash {
//     type Output = Result<DataType<T>, ErrorType>;

//     fn add(self, rhs: Result<DataType<T>, ErrorType>) -> Self::Output {
//         match rhs
//     }
// }

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
    value: atomic::AtomicType,
    span: Span,
}

#[derive(Debug, Clone, derive_more::From, derive_more::TryInto, derive_more::Display)]
pub enum FunctionType<Val>
where
    Val: Clone + PartialEq + Eq,
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
    Val: Clone + PartialEq + Eq,
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
    Val: Clone + PartialEq + Eq,
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
    Atomic(atomic::AtomicType),
    #[display(fmt = "symbol_{:#?}", _0)]
    Symbol(SymbolUsize),
    List(Vector<Val>),
    #[from(ignore)]
    Vector(Vector<Val>),
    HashMap(HashMap<atomic::AtomicType, Val>),
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
        DataType::Atomic(atomic::AtomicType::default())
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
pub struct DataValue {
    pub value: DataType<DataValue>,
    pub meta: HashMap<SymbolUsize, DataValue>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Spanned representation of Data values
pub struct SpannedValue(DataType<SpannedValue>, Span);

#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    /// Missing an ending character, show what it expects there to be
    UnbalancedParen(&'static str),
}

#[derive(Debug, Clone, PartialEq)]
pub enum EvalError {
    /// Function received not enough arguments to run
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
