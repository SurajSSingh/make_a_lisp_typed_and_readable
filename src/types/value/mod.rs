use fraction::GenericDecimal;
use im::{HashMap, HashSet, Vector};
use logos::Span;
use string_interner::symbol::SymbolUsize;

use crate::env::Env;

use super::MaltarResult;

mod atomic;

pub trait MaltarTrait: Clone + std::hash::Hash + Eq + Ord {}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CollectionValue<Val>
where
    Val: MaltarTrait,
{
    List(Vector<Val>),
    Vector(Vec<Val>),
    HashMap(HashMap<Val, Val>),
    HashSet(HashSet<Val>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FunctionValue<Val>
where
    Val: MaltarTrait,
{
    LiftedFunction {
        name: &'static str,
        // func: fn(&[Val]) -> MaltarResult<Val>,
    },
    Closure {
        ordered_params: Vec<SymbolUsize>,
        more_param_sym: Option<SymbolUsize>,
        exprs: Vec<Val>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MetadataType<Val>
where
    Val: MaltarTrait,
{
    Collection(CollectionValue<Val>),
    Function(FunctionValue<Val>),
    Symbol(SymbolUsize),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MetadataStruct<Val>
where
    Val: MaltarTrait,
{
    value: MetadataType<Val>,
    metadata: Box<Val>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MaltarValue<Val>
where
    Val: MaltarTrait,
{
    Atomic(atomic::AtomicValue),
    NonAtomic(MetadataStruct<Val>),
}

impl<Val> MaltarValue<Val>
where
    Val: MaltarTrait,
{
    pub fn try_as_symbol(&self) -> Option<SymbolUsize> {
        match self {
            MaltarValue::NonAtomic(MetadataStruct {
                value: MetadataType::Symbol(sym),
                ..
            }) => Some(*sym),
            _ => None,
        }
    }

    pub fn try_as_collection(&self) -> Option<CollectionValue<Val>> {
        match self {
            MaltarValue::NonAtomic(MetadataStruct {
                value: MetadataType::Collection(coll),
                ..
            }) => {
                // FIXME: this should likely return a (mutable) reference directly
                Some(coll.clone())
            }
            _ => None,
        }
    }

    pub fn eval_ast(self, env: &Env<Val>) -> MaltarResult<MaltarValue<Val>> {
        if let Some(sym) = self.try_as_symbol() {
            todo!()
        } else if let Some(coll) = self.try_as_collection() {
            todo!()
        } else {
            return Ok(self);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MaltarSpannedValue(MaltarValue<MaltarSpannedValue>, Span);

impl MaltarTrait for MaltarSpannedValue {}

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
