use std::ops::Range;

use im::Vector;
use imstr::ImString;

use crate::new_env::EnvStruct;

use super::DataValueResult;

#[derive(Debug, Clone, derive_more::From, derive_more::TryInto, derive_more::Display)]
/// These are values which can be applied
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
        is_macro: bool,
    },
}

impl<Val: Eq> Eq for FunctionType<Val> where Val: Clone + PartialEq + Eq {}

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
                    is_macro: l_is_macro,
                },
                Self::UserDefinedFunction {
                    name: r_name,
                    ast: r_ast,
                    params: r_params,
                    env: _r_env,
                    val: r_val,
                    is_macro: r_is_macro,
                },
            ) => {
                l_name == r_name
                    && l_ast == r_ast
                    && l_params == r_params
                    && l_val == r_val
                    && l_is_macro == r_is_macro
            }
            _ => false,
        }
    }
}

impl<Val> FunctionType<Val>
where
    Val: Clone + PartialEq + Eq,
{
    pub fn apply(&self, args: &[Val]) -> DataValueResult {
        todo!()
    }
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
