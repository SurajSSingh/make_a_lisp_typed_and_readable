pub mod atomic;
pub mod collection;
pub mod error;
pub mod function;

use im::{HashMap, HashSet, Vector};
use logos::Span;
use string_interner::symbol::SymbolUsize;

use self::collection::CollectionType;
use self::error::ErrorType;
use self::function::FunctionType;

pub type DataValueResult = Result<DataType, ErrorType>;

#[derive(
    Debug, Clone, PartialEq, Eq, derive_more::From, derive_more::TryInto, derive_more::Display,
)]
/// The data types represented by the program
pub enum DataValue<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    Atomic(atomic::AtomicType),
    Collection(CollectionType<Val>),
    Function(FunctionType<Val>),
}

impl<Val: std::hash::Hash> std::hash::Hash for DataValue<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // core::mem::discriminant(self).hash(state);
        todo!();
    }
}

impl<Val> Default for DataValue<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    fn default() -> Self {
        DataValue::Atomic(atomic::AtomicType::default())
    }
}

impl<Val> From<Option<DataValue<Val>>> for DataValue<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    fn from(value: Option<DataValue<Val>>) -> Self {
        value.unwrap_or_default()
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, derive_more::From, derive_more::TryInto, derive_more::Display,
)]
/// All types that can be evaluated
pub enum EvaluableType<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    Data(DataValue<Val>),
    #[display(fmt = "symbol_{:#?}", _0)]
    Symbol(SymbolUsize),
}

impl<Val> Default for EvaluableType<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    fn default() -> Self {
        EvaluableType::Data(DataValue::default())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Instances a data type recursively
pub struct DataType {
    pub value: EvaluableType<DataType>,
    pub meta: HashMap<SymbolUsize, DataType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Spanned representation of Data values
pub struct SpannedValue(DataValue<SpannedValue>, Span);
