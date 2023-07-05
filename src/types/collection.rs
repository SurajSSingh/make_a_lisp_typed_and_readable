use im::{HashMap, HashSet, Vector};

use super::atomic::AtomicType;

#[derive(
    Debug, Clone, PartialEq, Eq, derive_more::From, derive_more::TryInto, derive_more::Display,
)]
/// These are types which hold multiple types
pub enum CollectionType<Val>
where
    Val: Clone + PartialEq + Eq + std::hash::Hash,
{
    List(Vector<Val>),
    #[from(ignore)]
    Vector(Vector<Val>),
    HashMap(HashMap<AtomicType, Val>),
    HashSet(HashSet<Val>),
}
