use std::hash::BuildHasher;

use string_interner::{backend::Backend, StringInterner, Symbol};

use crate::types::{
    atomic::{self, AtomicType},
    DataType, DataValue,
};

use super::MalType;

/// Print out the AST expression
pub fn pr_str_old(ast: MalType, print_readably: bool) -> String {
    match ast {
        MalType::String(s) => {
            if print_readably {
                format!(
                    "\"{}\"",
                    s.chars()
                        .map(|c| match c {
                            '"' => "\\\"".to_string(),
                            '\n' => "\\n".to_string(),
                            '\\' => "\\\\".to_string(),
                            _ => c.to_string(),
                        })
                        .collect::<Vec<String>>()
                        .join("")
                )
            } else {
                s
            }
        }
        MalType::Nil(_) => String::from("nil"),
        MalType::Bool(b) => b.to_string(),
        MalType::Number(n) => n.to_string(),
        MalType::Keyword(k) => k,
        MalType::SpecialForm(k) => k.to_string(),
        MalType::Symbol(s) => s,
        MalType::List(l, _) => format!(
            "({})",
            l.into_iter()
                .map(|m| pr_str_old(m, print_readably))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        MalType::Vector(v, _) => format!(
            "[{}]",
            v.into_iter()
                .map(|m| pr_str_old(m, print_readably))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        MalType::Map(m, _) => format!(
            "{{{}}}",
            m.into_iter()
                .map(|(k, v)| format!(
                    "{} {}",
                    pr_str_old(k, print_readably),
                    pr_str_old(v, print_readably)
                ))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        MalType::LiftedFunc(n, _, _) => format!("Built-in Function: {n}"),
        MalType::MalFunc {
            fn_ast,
            params,
            fn_env: _,
            fn_val: _,
            is_macro: _,
            meta: _,
        } => format!("(fn* ({}) {fn_ast})", params.join(" ")),
        MalType::Atom(a) => format!("(atom {})", pr_str_old(a.borrow().clone(), print_readably)),
    }
}

pub fn pr_str(ast: DataValue, print_readably: bool) -> String {
    match ast.value {
        DataType::Symbol(s) => format!("symbol_{}", s.to_usize()),
        _ => todo!(),
    }
}

pub fn pr_str_with_resolver<B, H>(
    ast: DataValue,
    print_readably: bool,
    backend: StringInterner<B, H>,
) -> String
where
    B: Backend,
    H: BuildHasher,
{
    match ast.value {
        DataType::Atomic(atomic::AtomicType::Keyword(k)) => todo!(),
        DataType::Symbol(s) => todo!(),
        _ => pr_str(ast, print_readably),
        // DataType::Symbol(s) => match backend.resolve(s) {
        //     Some(i) => format!("{i}"),
        //     None => "Unknown Symbol".to_string(),
        // },
        // DataType::Atomic(AtomicType::Keyword(k)) => match backend.resolve(k) {
        //     Some(i) => format!("{i}"),
        //     None => "Unknown Symbol".to_string(),
        // },
        // _ => pr_str(ast, print_readably),
    }
}
