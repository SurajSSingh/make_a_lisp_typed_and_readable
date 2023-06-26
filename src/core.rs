use std::{cell::RefCell, fs::read_to_string, io::ErrorKind, iter::once, rc::Rc};

use super::{
    env::Env,
    eval, new_eval_error,
    printer::pr_str_old,
    reader::{read_str, MalType},
    rep, MalResult, ReplError,
};

/// Apply pr_str_old to each argument and join them together
pub fn stringify_args(args: Vec<MalType>, print_readably: bool, join_str: Option<&str>) -> String {
    args.into_iter()
        .map(|a| pr_str_old(a, print_readably))
        .collect::<Vec<_>>()
        .join(join_str.unwrap_or(""))
}
/// Makes each argument to their readable (escaped) string representation and concatenates them into a single string type.
pub fn pr_dash_str(args: Vec<MalType>) -> MalResult {
    Ok(MalType::String(stringify_args(args, true, Some(" "))))
}

/// Makes each argument to their string representation and concatenates them into a single string type.
pub fn str(args: Vec<MalType>) -> MalResult {
    Ok(MalType::String(stringify_args(args, false, None)))
}

/// Makes each argument to their readable (escaped) string representation, concatenates them, and then prints the result to console.
pub fn prn(args: Vec<MalType>) -> MalResult {
    println!("{}", stringify_args(args, true, Some(" ")));
    Ok(MalType::Nil(()))
}

/// Makes each argument to their string representation, concatenates them, and then prints the result to console.
pub fn println(args: Vec<MalType>) -> MalResult {
    println!("{}", stringify_args(args, false, Some(" ")));
    Ok(MalType::Nil(()))
}

/// Convert all arguments to a list
pub fn to_list(args: Vec<MalType>) -> MalResult {
    Ok(MalType::List(args, Box::new(MalType::Nil(()))))
}

/// Check if first argument is a list
pub fn is_list(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::List(_, _), ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Check if first argument is empty
pub fn is_empty(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::List(v, _) | MalType::Vector(v, _), ..] => Ok(MalType::Bool(v.is_empty())),
        [MalType::Map(m, _), ..] => Ok(MalType::Bool(m.is_empty())),
        [t, ..] => new_eval_error(format!(
            "Not a valid type; expected a list, vector, or map, but got {}",
            t.get_type()
        )),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Check the number of elements in first argument
pub fn count(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::List(v, _) | MalType::Vector(v, _), ..] => Ok(MalType::Number(v.len() as f64)),
        [MalType::Map(m, _), ..] => Ok(MalType::Number(m.len() as f64)),
        [MalType::Nil(()), ..] => Ok(MalType::Number(0.0)),
        [t, ..] => new_eval_error(format!(
            "Not a valid type; expected a list, vector, map, or nil, but got {}",
            t.get_type()
        )),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Read a string and tries to parse it to a MalType
pub fn read_string(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::String(string), ..] => read_str(string)
            .map(|m| *m)
            .map_err(super::ReplError::Parse),
        [_, ..] => new_eval_error("Not a string".to_string()),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Given a string path, return the contents of the file as a string
pub fn slurp(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::String(path), ..] => {
            read_to_string(path)
                .map(MalType::String)
                .map_err(|err| match err.kind() {
                    ErrorKind::NotFound => {
                        ReplError::Eval(format!("Could not read file: {path} does not exist"))
                    }
                    ErrorKind::PermissionDenied => ReplError::Eval(format!(
                        "Could not read file: you don't have permission to open {path}"
                    )),
                    ErrorKind::InvalidInput => {
                        ReplError::Eval("Could not read file: Invalid input".to_string())
                    }
                    ErrorKind::Interrupted => {
                        ReplError::Eval(format!("File read interrupted while reading: {path}"))
                    }

                    _ => ReplError::Eval("Unknown I/O error".to_string()),
                })
        }
        [_, ..] => new_eval_error("Path not a string".to_string()),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Make a given value into an atom
pub fn to_atom(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [a, ..] => Ok(MalType::Atom(Rc::new(RefCell::new(a.clone())))),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Check if a given value is an atom
pub fn is_atom(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Atom(_), ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Dereference an atom to its underlying value
pub fn deref(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Atom(a), ..] => Ok(a.borrow().clone()),
        [m, ..] => new_eval_error(format!("Cannot deref non-atom; got {}", m.get_type())),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Reset an atom to a different value
pub fn reset(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Atom(a), value, ..] => {
            a.replace(value.clone());
            Ok(value.clone())
        }
        [m, _, ..] => new_eval_error(format!("Cannot deref non-atom; got {}", m.get_type())),
        [] | [_] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Use a function to update the value of an atom
pub fn swap(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Atom(a), MalType::LiftedFunc(_, f, _), extra_args @ ..] => {
            let new_value = f(once(a.borrow().clone())
                .chain(extra_args.iter().cloned())
                .collect())?;
            a.replace(new_value.clone());
            Ok(new_value)
        }
        [MalType::Atom(a), MalType::MalFunc {
            fn_ast,
            params,
            fn_env,
            fn_val: _,
            is_macro: _,
            meta: _,
        }, extra_args @ ..] => {
            let env = Env::with_bindings(
                Some(fn_env.clone()),
                params,
                &once(a.borrow().clone())
                    .chain(extra_args.iter().cloned())
                    .collect::<Vec<_>>(),
            )?;
            let new_value = eval((**fn_ast).clone(), env)?;
            a.replace(new_value.clone());
            Ok(new_value)
        }
        [m, ..] => new_eval_error(format!("Cannot deref non-atom; got {}", m.get_type())),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Takes a first item and a second item list, put them together with first item prepened to the list
pub fn cons(args: Vec<MalType>) -> MalResult {
    // TODO: Use immutable data structure
    match args.as_slice() {
        [item, MalType::List(l, _) | MalType::Vector(l, _), ..] => Ok(MalType::List(
            once(item).chain(l.iter()).cloned().collect(),
            Box::new(MalType::Nil(())),
        )),
        [_, m, ..] => new_eval_error(format!("Second item must be a list; got {}", m.get_type())),
        [] | [_] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Takes 0 or more lists and concatenates them together
pub fn concat(args: Vec<MalType>) -> MalResult {
    // TODO: Use immutable data structure
    Ok(MalType::List(
        args.into_iter()
            .map_while(|l| match l {
                MalType::List(l, _) | MalType::Vector(l, _) => Some(l),
                _ => None,
            })
            .flatten()
            .collect(),
        Box::new(MalType::Nil(())),
    ))
}

/// Convert a list into a vector
pub fn vec(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::List(l, _), ..] => Ok(MalType::Vector(l.to_vec(), Box::new(MalType::Nil(())))),
        [v @ MalType::Vector(_, _), ..] => Ok(v.clone()),
        [m, ..] => new_eval_error(format!("Expect a list (or vector); got a {}", m.get_type())),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Get the nth item from a list or vector
pub fn nth(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::List(l, _) | MalType::Vector(l, _), MalType::Number(n), ..]
            if n.is_sign_positive() && n.is_finite() =>
        {
            l.get(*n as usize)
                .cloned()
                .ok_or(ReplError::Eval("Out of bounds".to_string()))
        }
        [MalType::List(_, _) | MalType::Vector(_, _), MalType::Number(n), ..] => new_eval_error(
            format!("Expect number to be an unsigned integer; got a {}", n),
        ),
        [MalType::List(_, _) | MalType::Vector(_, _), m, ..] => new_eval_error(format!(
            "Expect a number as the second argument; got a {}",
            m.get_type()
        )),
        [m, _, ..] => new_eval_error(format!(
            "Expect a list or vector as the first argument; got a {}",
            m.get_type()
        )),
        [] | [_] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Get the nth item from a list or vector
pub fn first(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::List(l, _) | MalType::Vector(l, _), ..] => Ok(l
            .split_first()
            .map(|(first, _)| first.clone())
            .unwrap_or(MalType::Nil(()))),
        [nil @ MalType::Nil(()), ..] => Ok(nil.clone()),
        [m, ..] => new_eval_error(format!(
            "Expect a list, vector, or nil as the first argument; got a {}",
            m.get_type()
        )),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Get the nth item from a list or vector
pub fn rest(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::List(l, _) | MalType::Vector(l, _), ..] => Ok(l
            .split_first()
            .map(|(_, rest)| MalType::List(rest.to_vec(), Box::new(MalType::Nil(()))))
            .unwrap_or(MalType::List(vec![], Box::new(MalType::Nil(()))))),
        [MalType::Nil(()), ..] => Ok(MalType::List(vec![], Box::new(MalType::Nil(())))),
        [m, ..] => new_eval_error(format!(
            "Expect a list, vector, or nil as the first argument; got a {}",
            m.get_type()
        )),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Throws the first argument as an exception
pub fn throw(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [exception, ..] => Err(ReplError::Exception(exception.clone())),
        [] => new_eval_error("No argument to throw".to_string()),
    }
}

/// Applies the first argument (as function) to the rest of the arguments
pub fn apply_fn(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::MalFunc {
            fn_ast,
            params,
            fn_env,
            fn_val: _,
            is_macro: _,
            meta: _,
        }, middle @ .., MalType::List(v, _) | MalType::Vector(v, _)] => {
            let mut a = middle.to_vec();
            a.extend_from_slice(v);
            let env = Env::with_bindings(Some(fn_env.clone()), params, &a)?;
            eval((**fn_ast).clone(), env)
        }
        // TODO: Change how concatenation is handled
        [MalType::LiftedFunc(_, f, _), middle @ .., MalType::List(v, _) | MalType::Vector(v, _)] => {
            let mut a = middle.to_vec();
            a.extend_from_slice(v);
            f(a)
        }
        [m, ..] => new_eval_error(format!("Expected a function, got {}", m.get_type())),
        [] => new_eval_error("No function given".to_string()),
    }
}

/// Maps the first argument (as function) to each of the rest of the arguments
pub fn map_fn(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::MalFunc {
            fn_ast,
            params,
            fn_env,
            fn_val: _,
            is_macro: _,
            meta: _,
        }, MalType::List(f_args, _) | MalType::Vector(f_args, _), ..] => Ok(MalType::List(
            f_args.iter().try_fold(Vec::new(), |mut vec, a| {
                let env = Env::with_bindings(Some(fn_env.clone()), params, &[a.clone()])?;
                match eval(*fn_ast.clone(), env) {
                    Ok(val) => {
                        vec.push(val);
                        Ok(vec)
                    }
                    Err(err) => Err(err),
                }
            })?,
            Box::new(MalType::Nil(())),
        )),
        [MalType::LiftedFunc(_, f, _), MalType::List(f_args, _) | MalType::Vector(f_args, _), ..] => {
            Ok(MalType::List(
                f_args
                    .iter()
                    .try_fold(Vec::new(), |mut vec, a| match f(vec![a.clone()]) {
                        Ok(val) => {
                            vec.push(val);
                            Ok(vec)
                        }
                        Err(err) => Err(err),
                    })?,
                Box::new(MalType::Nil(())),
            ))
        }
        [m, ..] => new_eval_error(format!("Expected a function, got {}", m.get_type())),
        [] => new_eval_error("No function given".to_string()),
    }
}

/// Check if first argument is nil value (exactly nil type, not empty collection)
pub fn is_nil(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Nil(()), ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Check if first argument is true value
pub fn is_true(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Bool(true), ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Check if first argument is false value
pub fn is_false(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Bool(false), ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Check if first argument is a symbol
pub fn is_symbol(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Symbol(_), ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Converts a string to a symbol with that string name
pub fn to_symbol(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::String(s), ..] => Ok(MalType::Symbol(s.clone())),
        [m, ..] => new_eval_error(format!("Cannot make symbol out of type {}", m.get_type())),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Converts a string into a keyword with that string name
pub fn to_keyword(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::String(s), ..] => Ok(MalType::Keyword(format!(":{s}"))),
        [keyword @ MalType::Keyword(_), ..] => Ok(keyword.clone()),
        [m, ..] => new_eval_error(format!("Cannot make symbol out of type {}", m.get_type())),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Checks if the first argument is a keyword
pub fn is_keyword(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Keyword(_), ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Collects variable number of arguments into a vector
pub fn to_vector(args: Vec<MalType>) -> MalResult {
    Ok(MalType::Vector(args, Box::new(MalType::Nil(()))))
}

/// Checks if the first argument is a vector
pub fn is_vector(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Vector(_, _), ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Checks if the first argument is a sequential type (list or vector)
pub fn is_sequential(args: Vec<MalType>) -> MalResult {
    match is_list(args.clone()) {
        Ok(MalType::Bool(true)) => Ok(MalType::Bool(true)),
        Ok(MalType::Bool(false)) => is_vector(args),
        Err(err) => Err(err),
        _ => new_eval_error("Non-boolean result found".to_string()),
    }
}

/// Create a hash map from key value pairs
pub fn to_hash_map(args: Vec<MalType>) -> MalResult {
    Ok(MalType::Map(
        args.chunks_exact(2)
            .map(|x| match x {
                [k, v] => (k.clone(), v.clone()),
                _ => panic!("Chunk size is incorrect"),
            })
            .collect(),
        Box::new(MalType::Nil(())),
    ))
}

/// Check if the first argument is a hash map
pub fn is_map(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Map(_, _), ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Create a new hash map from the merging of a starting hash map and a list of key-value pairs
///
/// FIXME: Inefficient checking because not using underlying hash map
pub fn assoc(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Map(m, _), kv @ ..] => {
            let updater = kv
                .chunks_exact(2)
                .map(|x| match x {
                    [k, v] => (k.clone(), v.clone()),
                    _ => panic!("Chunk size is incorrect"),
                })
                .collect::<Vec<_>>();
            let kept = m
                .iter()
                .filter(|(k1, _)| !updater.iter().any(|(k2, _)| k1 == k2))
                .chain(updater.iter())
                .cloned()
                .collect::<Vec<_>>();
            Ok(MalType::Map(kept, Box::new(MalType::Nil(()))))
        }
        [m, ..] => new_eval_error(format!("Expected a hashmap, got {}", m.get_type())),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Create a new hash map from the deletion of a starting hash map with a list of key-value pairs
///
/// FIXME: Inefficient checking because not using underlying hash map
pub fn dissoc(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Map(m, _), keys @ ..] => {
            let kept = m
                .iter()
                .filter(|(k1, _)| !keys.iter().any(|k2| k1 == k2))
                .cloned()
                .collect::<Vec<_>>();
            Ok(MalType::Map(kept, Box::new(MalType::Nil(()))))
        }
        [m, ..] => new_eval_error(format!("Expected a hashmap, got {}", m.get_type())),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Given a hash map and and key, get the value at the given key in the hash map or return nil
pub fn get(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Map(m, _), key, ..] => Ok(m
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.clone())
            .unwrap_or(MalType::Nil(()))),
        [MalType::Nil(()), ..] => Ok(MalType::Nil(())),
        [m, ..] => new_eval_error(format!("Expected a hashmap, got {}", m.get_type())),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Checks if a given hash map contains a given key
pub fn contains(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Map(m, _), key, ..] => Ok(MalType::Bool(m.iter().any(|(k, _)| k == key))),
        [m, ..] => new_eval_error(format!("Expected a hashmap, got {}", m.get_type())),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Return a list of keys
pub fn keys(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Map(m, _), ..] => Ok(MalType::List(
            m.iter().map(|(k, _)| k).cloned().collect(),
            Box::new(MalType::Nil(())),
        )),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Return a list of values
pub fn vals(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Map(m, _), ..] => Ok(MalType::List(
            m.iter().map(|(_, v)| v).cloned().collect(),
            Box::new(MalType::Nil(())),
        )),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Read a line from the user
pub fn readline(args: Vec<MalType>) -> MalResult {
    let mut r = rustyline::DefaultEditor::new()
        .map_err(|e| ReplError::Eval(format!("Editor Err: {}", e)))?;
    let response = r.readline(match args.as_slice() {
        [MalType::String(prompt), ..] => prompt,
        _ => "",
    });
    match response {
        Ok(line) => pr_dash_str(vec![super::read(line)?]),
        Err(rustyline::error::ReadlineError::Eof) => Ok(MalType::Nil(())),
        Err(err) => Err(ReplError::Eval(err.to_string())),
    }
}

/// The current time in nanoseconds from the UNIX epoch
pub fn time_ms(_args: Vec<MalType>) -> MalResult {
    use std::time::SystemTime;

    match SystemTime::now().duration_since(SystemTime::UNIX_EPOCH) {
        Ok(n) => Ok(MalType::Number(n.as_millis() as f64)),
        Err(_) => Err(ReplError::Eval("SystemTime before UNIX EPOCH!".to_string())),
    }
}

/// Get meta information of collection
pub fn meta(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::List(_, m)
        | MalType::Vector(_, m)
        | MalType::Map(_, m)
        | MalType::LiftedFunc(_, _, m)
        | MalType::MalFunc { meta: m, .. }, ..] => Ok((**m).clone()),
        [m, ..] => new_eval_error(format!("Type {} does not have metadata", m)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Add meta information to a collection
pub fn with_meta(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::List(val, _), data, ..] => {
            Ok(MalType::List(val.to_vec(), Box::new(data.clone())))
        }
        [MalType::Vector(val, _), data, ..] => {
            Ok(MalType::Vector(val.to_vec(), Box::new(data.clone())))
        }
        [MalType::Map(val, _), data, ..] => Ok(MalType::Map(val.to_vec(), Box::new(data.clone()))),
        [MalType::LiftedFunc(name, val, _), data, ..] => Ok(MalType::LiftedFunc(
            name.to_string(),
            *val,
            Box::new(data.clone()),
        )),
        [MalType::MalFunc {
            fn_ast,
            params,
            fn_env,
            fn_val,
            is_macro,
            meta: _,
        }, data, ..] => Ok(MalType::MalFunc {
            fn_ast: fn_ast.clone(),
            params: params.to_vec(),
            fn_env: fn_env.clone(),
            fn_val: fn_val.clone(),
            is_macro: *is_macro,
            meta: Box::new(data.clone()),
        }),
        [m, _, ..] => new_eval_error(format!("Type {} does not have metadata", m)),
        [] | [_] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Check if the first argument is string
pub fn is_string(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::String(_), ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Check if the first argument is number
pub fn is_number(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::Number(_), ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Check if the first argument is a function
pub fn is_function(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::LiftedFunc(_, _, _)
        | MalType::MalFunc {
            fn_ast: _,
            params: _,
            fn_env: _,
            fn_val: _,
            is_macro: false,
            meta: _,
        }, ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Check if the first argument is a macro
pub fn is_macro(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::MalFunc {
            fn_ast: _,
            params: _,
            fn_env: _,
            fn_val: _,
            is_macro: true,
            meta: _,
        }, ..] => Ok(MalType::Bool(true)),
        [_, ..] => Ok(MalType::Bool(false)),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Convert a sequence type into a list
pub fn seq(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::List(l, _) | MalType::Vector(l, _), ..] => Ok(if l.is_empty() {
            MalType::Nil(())
        } else {
            MalType::List(l.clone(), Box::new(MalType::Nil(())))
        }),
        [MalType::String(s), ..] => Ok(if s.is_empty() {
            MalType::Nil(())
        } else {
            MalType::List(
                s.chars().map(|c| MalType::String(c.to_string())).collect(),
                Box::new(MalType::Nil(())),
            )
        }),
        [MalType::Nil(_), ..] => Ok(MalType::Nil(())),
        [m, ..] => new_eval_error(format!(
            "Expected a list, vector, string or nil; got {}",
            m.get_type()
        )),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Take a collection and some elements and addes them to the collection.
/// For list, inserted from front in reverse order.
/// For vector, inserted to back in order.
pub fn conj(args: Vec<MalType>) -> MalResult {
    match args.as_slice() {
        [MalType::List(l, _), elem @ ..] => Ok(MalType::List(
            elem.iter().rev().chain(l.iter()).cloned().collect(),
            Box::new(MalType::Nil(())),
        )),
        [MalType::Vector(v, _), elem @ ..] => Ok(MalType::Vector(
            v.iter().chain(elem.iter()).cloned().collect(),
            Box::new(MalType::Nil(())),
        )),
        [m, ..] => new_eval_error(format!("Expected a list or vector; got {}", m.get_type())),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

/// Evaluates a given rust expression
pub fn rust_eval(args: Vec<MalType>) -> MalResult {
    if !args.is_empty() {
        return new_eval_error("Rust Evaluator not working".to_string());
    }
    if args.is_empty() {
        return new_eval_error("Not enough arguments".to_string());
    }
    let (mut context, _outputs) =
        evcxr::EvalContext::new().map_err(|err| ReplError::Eval(err.to_string()))?;
    match args.as_slice() {
        [MalType::String(code), ..] => context
            .eval(code)
            .map(|res| {
                res.content_by_mime_type
                    .get("text/plain")
                    .cloned()
                    .map(MalType::String)
                    .unwrap_or(MalType::Nil(()))
            })
            .map_err(|err| ReplError::Eval(err.to_string())),
        [m, ..] => new_eval_error(format!("Expected a string; got {}", m.get_type())),
        [] => new_eval_error("Not enough arguments".to_string()),
    }
}

macro_rules! set_lift_op {
    // Unary operator
    ($repl_env:ident add $sym:expr, $func:path : $in_t1: path => $out_type:path) => {
        $repl_env.set(
            $sym.to_string(),
            MalType::LiftedFunc(stringify!($func).to_string(), |args| {
                let func_name = stringify!($func).split("::").last().unwrap();
                match args.as_slice(){
                    [$in_t1(x),..] => Ok($out_type($func(x))),
                    [other,..] => Err(format!(
                        "{func_name} function does not work for given type."
                    )),
                    [] => Err(format!("Not enough arguments for {func_name}"))
                }
            }),
        ).expect("Macro did not set core function properly")
    };
    // Binary operator - non default
    ($repl_env:ident += $sym:expr, $func:path : $($in_t1: path, $in_t2: path)|+ => $out_type:path) => {
        $repl_env.set(
            &MalType::Symbol($sym.to_string()),
            MalType::LiftedFunc(stringify!($func).to_string(), |args| {
                let func_name = stringify!($func).split("::").last().unwrap();
                match args.as_slice(){
                    $(
                        [$in_t1(x), $in_t2(y), ..] => Ok($out_type($func(x, y)))
                    ),+,
                    [_, _, ..] => new_eval_error(format!(
                        "{func_name} function does not work for given type."
                    )),
                    [] | [_] => new_eval_error(format!("Not enough arguments for {func_name}")),
                }
            },Box::new(MalType::Nil(()))),
        ).expect("Macro did not set core function properly")
    };
    // Binary operator - default
    ($repl_env:ident += $sym:expr, $func:path : any => $out_type:path) => {
        $repl_env.set(
            &MalType::Symbol($sym.to_string()),
            MalType::LiftedFunc(stringify!($func).to_string(), |args| {
                let func_name = stringify!($func).split("::").last().unwrap();
                match args.as_slice(){
                    [x, y, ..] => Ok($out_type($func(x, y))),
                    [] | [_] => new_eval_error(format!("Not enough arguments for {func_name}")),
                }
            },Box::new(MalType::Nil(()))),
        ).expect("Macro did not set core function properly")
    };
}

macro_rules! set_core_fn {
    ($repl_env:ident += $func:ident as $name:expr , $pretty_name:expr) => {
        $repl_env
            .set(
                &MalType::Symbol($name.to_string()),
                MalType::LiftedFunc($pretty_name.to_string(), $func, Box::new(MalType::Nil(()))),
            )
            .expect("Macro did not set core function properly");
    };
    ($repl_env:ident += $func:ident as $name:expr) => {
        $repl_env
            .set(
                &MalType::Symbol($name.to_string()),
                MalType::LiftedFunc(
                    stringify!($func).to_string(),
                    $func,
                    Box::new(MalType::Nil(())),
                ),
            )
            .expect("Macro did not set core function properly");
    };
    ($repl_env:ident += $func:ident , $pretty_name:expr) => {
        $repl_env
            .set(
                &MalType::Symbol(stringify!($func).to_string()),
                MalType::LiftedFunc($pretty_name.to_string(), $func, Box::new(MalType::Nil(()))),
            )
            .expect("Macro did not set core function properly");
    };
    ($repl_env:ident += $func:ident) => {
        $repl_env
            .set(
                &MalType::Symbol(stringify!($func).to_string()),
                MalType::LiftedFunc(
                    stringify!($func).to_string(),
                    $func,
                    Box::new(MalType::Nil(())),
                ),
            )
            .expect("Macro did not set core function properly");
    };
}

/// Creates a new environment with basic 4 function arithmetic operations
pub fn create_core_namespace() -> Env {
    let mut env = Env::default();

    // Lifted operations from Rust
    set_lift_op!(env += "+", std::ops::Add::add : MalType::Number, MalType::Number => MalType::Number);
    set_lift_op!(env += "-", std::ops::Sub::sub : MalType::Number, MalType::Number => MalType::Number);
    set_lift_op!(env += "*", std::ops::Mul::mul : MalType::Number, MalType::Number => MalType::Number);
    set_lift_op!(env += "/", std::ops::Div::div : MalType::Number, MalType::Number => MalType::Number);
    set_lift_op!(env += ">", std::cmp::PartialOrd::gt: MalType::Number, MalType::Number => MalType::Bool);
    set_lift_op!(env += "<", std::cmp::PartialOrd::lt : MalType::Number, MalType::Number => MalType::Bool);
    set_lift_op!(env += ">=", std::cmp::PartialOrd::ge : MalType::Number, MalType::Number => MalType::Bool);
    set_lift_op!(env += "<=", std::cmp::PartialOrd::le : MalType::Number, MalType::Number => MalType::Bool);
    set_lift_op!(env += "=", std::cmp::PartialEq::eq :  any => MalType::Bool);

    // Pre-defined core functions
    set_core_fn!(env += pr_dash_str as "pr-str");
    set_core_fn!(env += str);
    set_core_fn!(env += prn, "print");
    set_core_fn!(env += println);
    set_core_fn!(env += to_list as "list", "make list");
    set_core_fn!(env += is_list as "list?");
    set_core_fn!(env += is_empty as "empty?");
    set_core_fn!(env += count);
    set_core_fn!(env += read_string as "read-string");
    set_core_fn!(env += slurp);
    set_core_fn!(env += to_atom as "atom");
    set_core_fn!(env += is_atom as "atom?");
    set_core_fn!(env += deref);
    set_core_fn!(env += reset as "reset!");
    set_core_fn!(env += swap as "swap!");
    set_core_fn!(env += cons);
    set_core_fn!(env += concat);
    set_core_fn!(env += vec);
    set_core_fn!(env += nth);
    set_core_fn!(env += first);
    set_core_fn!(env += rest);
    set_core_fn!(env += throw);
    set_core_fn!(env += apply_fn as "apply");
    set_core_fn!(env += map_fn as "map");
    set_core_fn!(env += is_nil as "nil?");
    set_core_fn!(env += is_true as "true?");
    set_core_fn!(env += is_false as "false?");
    set_core_fn!(env += is_symbol as "symbol?");
    set_core_fn!(env += to_symbol as "symbol");
    set_core_fn!(env += is_keyword as "keyword?");
    set_core_fn!(env += to_keyword as "keyword");
    set_core_fn!(env += is_vector as "vector?");
    set_core_fn!(env += to_vector as "vector");
    set_core_fn!(env += is_sequential as "sequential?");
    set_core_fn!(env += to_hash_map as "hash-map");
    set_core_fn!(env += is_map  as "map?");
    set_core_fn!(env += assoc);
    set_core_fn!(env += dissoc);
    set_core_fn!(env += get);
    set_core_fn!(env += contains as "contains?");
    set_core_fn!(env += keys);
    set_core_fn!(env += vals);
    set_core_fn!(env += readline);
    set_core_fn!(env += time_ms as "time-ms");
    set_core_fn!(env += is_string as "string?");
    set_core_fn!(env += is_number as "number?");
    set_core_fn!(env += is_function as "fn?");
    set_core_fn!(env += is_macro as "macro?");
    set_core_fn!(env += seq);
    set_core_fn!(env += conj);
    set_core_fn!(env += meta);
    set_core_fn!(env += with_meta as "with-meta");
    // set_core_fn!(env += rust_eval as "rust-eval");

    env.set(
        &MalType::Symbol("*ARGV*".to_string()),
        MalType::List(vec![], Box::new(MalType::Nil(()))),
    )
    .expect("Could not assign *ARGV*");

    env
}

/// A function that adds some predefined function as user defined function
pub fn add_premade_lisp_fn_to(env: &mut Env) -> &mut Env {
    // Set Host Language
    rep(String::from("(def! *host-language* \"rust-mal\")"), env).unwrap();
    // Not function
    rep(String::from("(def! not (fn* (a) (if a false true)))"), env).unwrap();
    // Load file function
    rep(
        String::from(
            r#"(def! load-file (fn* (f) (eval (read-string (str "(do " (slurp f) "\nnil)")))))"#,
        ),
        env,
    )
    .unwrap();
    rep(String::from("(defmacro! cond (fn* (& xs) (if (> (count xs) 0) (list 'if (first xs) (if (> (count xs) 1) (nth xs 1) (throw \"odd number of forms to cond\")) (cons 'cond (rest (rest xs)))))))"), env).unwrap();
    env
}
