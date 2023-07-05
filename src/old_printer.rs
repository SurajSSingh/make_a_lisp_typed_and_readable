use super::MalType;

/// Print out the AST expression
pub fn pr_str(ast: MalType, print_readably: bool) -> String {
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
                .map(|m| pr_str(m, print_readably))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        MalType::Vector(v, _) => format!(
            "[{}]",
            v.into_iter()
                .map(|m| pr_str(m, print_readably))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        MalType::Map(m, _) => format!(
            "{{{}}}",
            m.into_iter()
                .map(|(k, v)| format!(
                    "{} {}",
                    pr_str(k, print_readably),
                    pr_str(v, print_readably)
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
        MalType::Atom(a) => format!("(atom {})", pr_str(a.borrow().clone(), print_readably)),
    }
}
