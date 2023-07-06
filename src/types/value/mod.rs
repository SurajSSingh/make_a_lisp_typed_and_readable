use fraction::GenericDecimal;
use im::{HashMap, HashSet, Vector};
use imstr::ImString;
use kstring::KString;
use logos::Span;
use string_interner::symbol::SymbolUsize;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AtomicValue {
    Nil(()),
    Bool(bool),
    Float(GenericDecimal<u64, u16>),
    String(ImString),
    Keyword(KString),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CollectionValue<Val>
where
    Val: Clone + std::hash::Hash + Eq + Ord,
{
    List(Vector<Val>),
    Vector(Vector<Val>),
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
    Atomic(AtomicValue),
    Collection(CollectionValue<Val>),
    Function(FunctionValue),
    Var(SymbolUsize),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MaltarSpannedValue(MaltarValue<MaltarSpannedValue>, Span);

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
