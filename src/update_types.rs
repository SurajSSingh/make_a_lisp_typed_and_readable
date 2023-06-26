// Add these to cargo
//
// ordered-float = "3.7.0"
// im = "15.1.0"

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum MalAtomic {
    #[default]
    Nil,
    Bool(bool),
    Number(OrderedFloat<f64>),
    Keyword(String),
    String(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum MalComposite {
    List(Vec<MalValue>),
    Vector(Vec<MalValue>),
    Map(HashMap<MalAtomic, MalValue>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum MalFunction {
    Lifted(String, fn(Vec<MalValue>) -> MalResult),
    User {
        ast: Box<MalValue>,
        params: Vec<String>,
        env: Env,
        val: Box<MalValue>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum MalValue {
    Atomic(MalAtomic),
    Composite(MalComposite),
    Function(MalFunction),
    Symbol(String),
}
