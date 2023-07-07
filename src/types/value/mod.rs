use fraction::GenericDecimal;
use im::{HashMap, HashSet, Vector};
use logos::Span;
use string_interner::symbol::SymbolUsize;

use crate::env::Env;

use super::MaltarResult;

mod atomic;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CollectionValue<Val>
where
    Val: Clone + std::hash::Hash + Eq + Ord,
{
    List(Vector<Val>),
    Vector(Vec<Val>),
    HashMap(HashMap<Val, Val>),
    HashSet(HashSet<Val>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FunctionValue {
    LiftedFunction {},
    Closure {},
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MaltarValue<Val>
where
    Val: Clone + std::hash::Hash + Eq + Ord,
{
    Atomic(atomic::AtomicValue),
    Collection(CollectionValue<Val>),
    Function(FunctionValue),
    Symbol(SymbolUsize),
}

impl<Val> MaltarValue<Val>
where
    Val: Clone + std::hash::Hash + Eq + Ord,
{
    pub fn eval_ast(self, env: &Env<Val>) -> MaltarResult<MaltarValue<Val>> {
        match self {
            MaltarValue::Symbol(_) => todo!(),
            MaltarValue::Collection(_) => todo!(),
            _ => Ok(self),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MaltarSpannedValue(MaltarValue<MaltarSpannedValue>, Span);

impl From<MaltarSpannedValue> for MaltarValue<MaltarSpannedValue> {
    fn from(val: MaltarSpannedValue) -> Self {
        val.0
    }
}

impl PartialOrd for MaltarSpannedValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for MaltarSpannedValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}
