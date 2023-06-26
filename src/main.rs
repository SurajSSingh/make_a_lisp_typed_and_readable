//! This is an implemtation of [MAL](https://github.com/kanaka/mal/), a simple lisp dialect inspired by Clojure
#![deny(missing_docs)]
use std::error::Error;

use reader::{MalType, ParseError};
use rustyline::{error::ReadlineError, DefaultEditor};

use env::Env;

use self::{
    core::{add_premade_lisp_fn_to, create_core_namespace},
    reader::SpecialKeyword,
};

mod core;
mod env;
mod new_env;
mod printer;
mod reader;
mod types;
/// Either results in a MAL type or gives back a message for an error
pub type MalResult = Result<MalType, ReplError>;

#[derive(Debug, Clone)]
/// Union of all the types of errors in the program
pub enum ReplError {
    /// Error in Parsing
    Parse(ParseError),
    /// Error in Evaluation
    Eval(String),
    /// Runtime Exception
    Exception(MalType),
}

/// Create a new REPL Eval error
fn new_eval_error<T>(msg: String) -> Result<T, ReplError> {
    Err(ReplError::Eval(msg))
}

/// Read in a string and parse it into an AST expression
fn read(line: String) -> MalResult {
    let expr = *reader::read_str(&line).map_err(ReplError::Parse)?;
    Ok(expr)
}

/// Evaluate an expression with a given environment
fn eval_ast(expr: MalType, env: Env) -> MalResult {
    match expr {
        sym @ MalType::Symbol(_) => env.get(&sym),
        ref typ @ MalType::List(ref list, _) | ref typ @ MalType::Vector(ref list, _) => {
            let new_list = list.iter().map(|e| eval(e.clone(), env.clone())).try_fold(
                Vec::new(),
                |mut list, r| {
                    if let Ok(e) = r {
                        list.push(e);
                        Ok(list)
                    } else {
                        Err(r.unwrap_err())
                    }
                },
            );
            match typ {
                MalType::List(_,meta) => new_list.map(|nl| MalType::List(nl, meta.clone())),
                MalType::Vector(_,meta) => new_list.map(|nl|MalType::Vector(nl, meta.clone())),
                _ => unreachable!("MalType not a vector or list but we bound to it in the previous match, impossible!")
            }
        }
        MalType::Map(m, meta) => {
            let new_map = m
                .iter()
                .map(|(k, v)| (k, eval(v.clone(), env.clone())))
                .try_fold(Vec::new(), |mut map, (k, r)| {
                    if let Ok(e) = r {
                        map.push((k.to_owned(), e));
                        Ok(map)
                    } else {
                        Err(r.unwrap_err())
                    }
                });
            new_map.map(|nm| MalType::Map(nm, meta.clone()))
        }
        _ => Ok(expr),
    }
}

fn quasiquote(ast: MalType) -> MalType {
    match ast {
        MalType::List(ref l, _) => match l.as_slice() {
            [MalType::SpecialForm(SpecialKeyword::Unquote), sec, ..] => sec.clone(),
            _ => {
                let mut current_result = MalType::List(vec![], Box::new(MalType::Nil(())));
                for elt in l.iter().rev() {
                    if let MalType::List(el, _) = elt {
                        if let Some(MalType::SpecialForm(SpecialKeyword::SpliceUnquote)) = el.get(0)
                        {
                            if let Some(sec) = el.get(1) {
                                current_result = MalType::List(
                                    vec![
                                        MalType::Symbol("concat".to_string()),
                                        sec.clone(),
                                        current_result.clone(),
                                    ],
                                    Box::new(MalType::Nil(())),
                                );

                                continue;
                            }
                        }
                    }
                    current_result = MalType::List(
                        vec![
                            MalType::Symbol("cons".to_string()),
                            quasiquote(elt.clone()),
                            current_result.clone(),
                        ],
                        Box::new(MalType::Nil(())),
                    );
                }
                current_result
            }
        },
        MalType::Vector(v, _) => {
            let mut current_result = MalType::List(vec![], Box::new(MalType::Nil(())));
            for elt in v.iter().rev() {
                if let MalType::List(el, _) = elt {
                    if let Some(MalType::SpecialForm(SpecialKeyword::SpliceUnquote)) = el.get(0) {
                        if let Some(sec) = el.get(1) {
                            current_result = MalType::List(
                                vec![
                                    MalType::Symbol("concat".to_string()),
                                    sec.clone(),
                                    current_result.clone(),
                                ],
                                Box::new(MalType::Nil(())),
                            );

                            continue;
                        }
                    }
                }
                current_result = MalType::List(
                    vec![
                        MalType::Symbol("cons".to_string()),
                        quasiquote(elt.clone()),
                        current_result.clone(),
                    ],
                    Box::new(MalType::Nil(())),
                );
            }
            MalType::List(
                vec![MalType::Symbol("vec".to_string()), current_result],
                Box::new(MalType::Nil(())),
            )
        }
        typ @ MalType::Map(_, _) | typ @ MalType::Symbol(_) => MalType::List(
            vec![MalType::SpecialForm(SpecialKeyword::Quote), typ],
            Box::new(MalType::Nil(())),
        ),
        _ => ast,
    }
}

/// Check if ast is a macro call; if it is, it returns the macro and the ast it applies to.
///
/// Slight modification from instruction to allow immediately returning the macro.
/// Can emulate the actual behavior by calling `.is_some()` on the result.
fn is_macro_call(ast: MalType, env: &Env) -> Option<(MalType, Vec<MalType>)> {
    if let MalType::List(l, _) = ast {
        if let Some((sym @ MalType::Symbol(_), rest)) = l.split_first() {
            if let Ok(
                mac @ MalType::MalFunc {
                    fn_ast: _,
                    params: _,
                    fn_env: _,
                    fn_val: _,
                    is_macro: true,
                    meta: _,
                },
            ) = env.get(sym)
            {
                return Some((mac, rest.to_vec()));
            }
        }
    }
    None
}

/// Evaluates a given macro within an environment and returns its expanded form
fn macroexpand(ast: MalType, env: &Env) -> MalResult {
    let mut current_ast = ast;
    while let Some((
        MalType::MalFunc {
            fn_ast,
            params,
            fn_env,
            fn_val: _,
            is_macro: _,
            meta: _,
        },
        macro_args,
    )) = is_macro_call(current_ast.clone(), env)
    {
        let new_env = Env::with_bindings(Some(fn_env), &params, &macro_args)?;
        current_ast = eval(*fn_ast, new_env)?;
    }
    Ok(current_ast)
}

/// Evaluate the given expression and return the result
fn eval(ast: MalType, env: Env) -> MalResult {
    let mut current_ast = ast;
    let mut current_env = env;
    let return_value: Result<MalType, ReplError> = 'tco: loop {
        // Apply expand macro
        if let MalType::List(_, _) = current_ast.clone() {
            current_ast = macroexpand(current_ast.clone(), &current_env)?;
        }
        // Else skipped, as the result will be the same in the switch

        // Evaluation "switch"
        if let MalType::List(ast_expr, _) = current_ast.clone() {
            match ast_expr.as_slice() {
                // Special case #1: Empty list
                [] => break 'tco Ok(current_ast),
                // Special case #2: Eval is within the current ast
                [MalType::Symbol(s), arg, ..] if s == "eval" => {
                    current_ast = eval(arg.clone(), current_env.clone())?;
                    // HACK: Eval creates new environment, need to bring back up.
                    while let Some(outer) = current_env.outer() {
                        current_env = outer;
                    }
                    continue 'tco;
                }
                [MalType::SpecialForm(SpecialKeyword::Def), key @ MalType::Symbol(_), val, ..] => {
                    let evaluated = eval(val.clone(), current_env.clone())?;
                    break 'tco current_env.set(key, evaluated);
                }
                [MalType::SpecialForm(SpecialKeyword::Def), MalType::Symbol(s)] => {
                    break 'tco new_eval_error(format!("No value to bind to symbol {s}"))
                }
                [MalType::SpecialForm(SpecialKeyword::Def)] => {
                    break 'tco new_eval_error("No symbol to define".to_string())
                }
                [MalType::SpecialForm(SpecialKeyword::Def), ..] => {
                    break 'tco new_eval_error("Not a valid def-form".to_string())
                }
                [MalType::SpecialForm(SpecialKeyword::Let), MalType::List(binds, _) | MalType::Vector(binds, _), let_ast, ..] =>
                {
                    current_env = Env::new(Some(current_env.clone()));
                    for (key, val) in binds.iter().step_by(2).zip(binds.iter().skip(1).step_by(2)) {
                        match key {
                            sym @ MalType::Symbol(_) => {
                                let evaluated_val = eval(val.clone(), current_env.clone())?;
                                current_env.set(sym, evaluated_val)?;
                            }
                            _ => {
                                break 'tco new_eval_error(format!(
                                    "Binding to non-symbol: {}",
                                    key
                                ))
                            }
                        }
                    }
                    current_ast = let_ast.clone();
                    continue 'tco;
                }
                [MalType::SpecialForm(SpecialKeyword::Let), MalType::List(_, _) | MalType::Vector(_, _)] => {
                    break 'tco new_eval_error(
                        "No item to process in let*; empty list or vector".to_string(),
                    )
                }
                [MalType::SpecialForm(SpecialKeyword::Let)] => {
                    break 'tco new_eval_error("No bindings found".to_string())
                }
                [MalType::SpecialForm(SpecialKeyword::Do), between @ .., last] => {
                    let _ = eval_ast(
                        MalType::List(between.to_vec(), Box::new(MalType::Nil(()))),
                        current_env.clone(),
                    );
                    current_ast = last.clone();
                    continue 'tco;
                }
                [MalType::SpecialForm(SpecialKeyword::Do)] => {
                    break 'tco new_eval_error("Do form has nothing to do".to_string())
                }
                [MalType::SpecialForm(SpecialKeyword::If), condition, true_case, false_case_plus_rest @ ..] =>
                {
                    if let MalType::Bool(false) | MalType::Nil(()) =
                        eval(condition.clone(), current_env.clone())?
                    {
                        current_ast = false_case_plus_rest
                            .first()
                            .cloned()
                            .unwrap_or(MalType::Nil(()));
                    } else {
                        current_ast = true_case.clone();
                    }
                    continue 'tco;
                }
                [MalType::SpecialForm(SpecialKeyword::If), _] => {
                    break 'tco new_eval_error("No cases to evaluate after condition".to_string());
                }
                [MalType::SpecialForm(SpecialKeyword::If)] => {
                    break 'tco new_eval_error("No condition to evaluate".to_string());
                }
                [MalType::SpecialForm(SpecialKeyword::Fn), MalType::List(param_syms, _) | MalType::Vector(param_syms, _), fn_ast, ..] =>
                {
                    let Ok(params) = param_syms.iter().try_fold(Vec::new(), |mut list, sym| {
                        if let MalType::Symbol(s) = sym {
                            list.push(s.clone());
                            Ok(list)
                        } else {
                            Err(())
                        }
                    }) else {
                        break 'tco new_eval_error("Parameters must all be symbols".to_string())
                    };
                    break 'tco Ok(MalType::MalFunc {
                        fn_ast: Box::new(fn_ast.clone()),
                        params,
                        fn_env: current_env.clone(),
                        fn_val: Box::new(MalType::Nil(())),
                        is_macro: false,
                        meta: Box::new(MalType::Nil(())),
                    });
                }
                [MalType::SpecialForm(SpecialKeyword::Fn), MalType::List(_, _) | MalType::Vector(_, _)] => {
                    break 'tco new_eval_error("Function definition has no body".to_string())
                }
                [MalType::SpecialForm(SpecialKeyword::Fn), _, ..] => {
                    break 'tco new_eval_error(
                        "Function parameters must be a list or vector".to_string(),
                    )
                }
                [MalType::SpecialForm(SpecialKeyword::Fn)] => {
                    break 'tco new_eval_error(
                        "Function definition got no parameters list".to_string(),
                    )
                }
                [MalType::SpecialForm(SpecialKeyword::Quote), quoted, ..] => {
                    break 'tco Ok(quoted.clone())
                }
                [MalType::SpecialForm(SpecialKeyword::Quote)] => {
                    break 'tco new_eval_error("Nothing is quoted".to_string())
                }
                [MalType::SpecialForm(SpecialKeyword::Quasiquote), qqast, ..] => {
                    current_ast = quasiquote(qqast.clone());
                    continue 'tco;
                }
                [MalType::SpecialForm(SpecialKeyword::Quasiquote)] => {
                    break 'tco new_eval_error("Nothing to quasi-quoted".to_string())
                }
                [MalType::Symbol(s), arg, ..] if s == "quasiquoteexpand" => {
                    break 'tco Ok(quasiquote(arg.clone()));
                }
                [MalType::Symbol(s)] if s == "quasiquoteexpand" => {
                    break 'tco new_eval_error("Nothing to quasi-quoted".to_string())
                }
                [MalType::SpecialForm(SpecialKeyword::DefMacro), key @ MalType::Symbol(_), mform, ..] =>
                {
                    let MalType::MalFunc { fn_ast, params, fn_env, fn_val, is_macro: _ , meta:_} = eval(mform.clone(), current_env.clone())? else {
                        break 'tco new_eval_error("Did not evaluate a macro".to_string());
                    };
                    break 'tco current_env.set(
                        key,
                        MalType::MalFunc {
                            fn_ast,
                            params,
                            fn_env,
                            fn_val,
                            is_macro: true,
                            meta: Box::new(MalType::Nil(())),
                        },
                    );
                }
                [MalType::SpecialForm(SpecialKeyword::DefMacro), _, ..] => {
                    break 'tco new_eval_error("Not a valid macro definition.".to_string())
                }
                [MalType::SpecialForm(SpecialKeyword::DefMacro)] => {
                    break 'tco new_eval_error("No macro to define.".to_string())
                }
                [MalType::SpecialForm(SpecialKeyword::MacroExpand), mform, ..] => {
                    break macroexpand(mform.clone(), &current_env)
                }
                [MalType::SpecialForm(SpecialKeyword::Try), a, MalType::List(catch_part, _), ..] => {
                    match catch_part.as_slice() {
                        [MalType::SpecialForm(SpecialKeyword::Catch), MalType::Symbol(b), c, ..] => {
                            match eval(a.clone(), current_env.clone()) {
                                Ok(res) => break 'tco Ok(res),
                                Err(ReplError::Exception(val)) => {
                                    current_env = Env::with_bindings(
                                        Some(current_env),
                                        &[b.clone()],
                                        &[val],
                                    )?;
                                    break 'tco eval(c.clone(), current_env);
                                }
                                Err(ReplError::Eval(msg)) => {
                                    current_env = Env::with_bindings(
                                        Some(current_env),
                                        &[b.clone()],
                                        &[MalType::String(msg)],
                                    )?;
                                    break 'tco eval(c.clone(), current_env);
                                }
                                _ => unimplemented!(),
                            }
                        }
                        [MalType::SpecialForm(SpecialKeyword::Catch), MalType::Symbol(_)] => {
                            break 'tco new_eval_error("No code to run for catch".to_string())
                        }
                        [MalType::SpecialForm(SpecialKeyword::Catch), m, ..] => {
                            break 'tco new_eval_error(format!(
                                "Expect a symbol for first argument of catch*, got {}",
                                m.get_type()
                            ))
                        }
                        [] | [_, ..] => break 'tco new_eval_error("Try has no catch".to_string()),
                    }
                }
                [MalType::SpecialForm(SpecialKeyword::Try), ..] => {
                    break 'tco new_eval_error("Try has nothing to try".to_string())
                }
                _ => match eval_ast(current_ast, current_env) {
                    Ok(MalType::List(res_list, _)) => match res_list.as_slice() {
                        [MalType::LiftedFunc(_, f, _), args @ ..] => break 'tco f(args.into()),
                        [MalType::MalFunc {
                            fn_ast,
                            params,
                            fn_env,
                            fn_val: _,
                            is_macro: false,
                            meta: _,
                        }, args @ ..] => {
                            current_ast = (**fn_ast).clone();
                            current_env = Env::with_bindings(Some(fn_env.clone()), params, args)?;
                        }
                        [item, ..] => {
                            break 'tco new_eval_error(format!(
                                "Expected first item to be a function; found {}",
                                item.get_type(),
                            ))
                        }
                        [] => {
                            break 'tco new_eval_error(
                                "Function not found; got back empty list".to_string(),
                            )
                        }
                    },
                    Ok(item) => {
                        break 'tco new_eval_error(format!(
                            "Expected a list; got {}",
                            item.get_type()
                        ))
                    }
                    Err(err) => break 'tco Err(err),
                },
            };
        } else {
            // Otherwise (not a list), just evaluate the ast and return the result
            break 'tco eval_ast(current_ast, current_env.clone());
        }
    };
    return_value
}

/// Print a given AST
fn print(value: MalType) {
    println!("{}", printer::pr_str_old(value, true))
}

/// Runs the read, evaluate, and print functions in that order
fn rep(line: String, env: &Env) -> Result<(), ReplError> {
    let ast = read(line)?;
    let res = eval(ast, env.clone())?;
    print(res);
    Ok(())
}

/// Read a file if given and get command line arguments
pub fn get_cmd_args(env: &mut Env) -> Option<String> {
    let mut args = std::env::args().skip(1);
    let Some(file_name) = args.next() else {
        return None;
    };
    let rest = args.map(MalType::String).collect();
    let _ = env.set(
        &MalType::Symbol("*ARGV*".to_string()),
        MalType::List(rest, Box::new(MalType::Nil(()))),
    );
    Some(file_name)
}

/// Runs the repl
pub fn repl() -> rustyline::Result<()> {
    // evcxr::runtime_hook();
    let mut rl = DefaultEditor::new()?;
    let mut repl_env = create_core_namespace();
    add_premade_lisp_fn_to(&mut repl_env);
    if let Some(file) = get_cmd_args(&mut repl_env) {
        let line = format!("(load-file \"{}\")", file);
        if let Err(err) = rep(line, &repl_env) {
            match err {
                ReplError::Parse(ParseError::UnbalancedParen) => {
                    println!("Unbalanced Paren");
                }
                ReplError::Eval(err) => {
                    println!("Eval Error: {}", err);
                }
                _ => {
                    println!("Unknown Error: {:?}", err);
                }
            }
        };
        return Ok(());
    }
    let _ = rep(
        r#"(println (str "Mal [" *host-language* "]"))"#.to_string(),
        &repl_env,
    );
    loop {
        let line = match rl.readline("user> ") {
            Ok(line) => line,
            Err(ReadlineError::Interrupted) => continue,
            Err(ReadlineError::Eof) => break,
            Err(err) => {
                println!("{}", err);
                break;
            }
        };
        rl.add_history_entry(line.clone())?;
        if let Err(err) = rep(line, &repl_env) {
            match err {
                ReplError::Parse(ParseError::UnbalancedParen) => {
                    println!("Unbalanced Paren");
                }
                ReplError::Eval(err) => {
                    println!("Eval Error: {}", err);
                }
                _ => {
                    println!("Unknown Error: {:?}", err);
                    break;
                }
            }
        }
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    use string_interner::StringInterner;
    let mut interner = StringInterner::default();
    let _sym0 = interner.get_or_intern("Elephant");
    Ok(repl()?)
}

#[cfg(test)]
mod tests {
    use super::{
        core::{add_premade_lisp_fn_to, create_core_namespace},
        *,
    };
    static mut OUTPUT: Vec<String> = vec![];

    pub fn simulate_print(args: Vec<MalType>) -> MalResult {
        let string = core::stringify_args(args, true, Some(" "));
        unsafe { OUTPUT.push(string) };
        Ok(MalType::Nil(()))
    }
    pub fn simulate_println(args: Vec<MalType>) -> MalResult {
        let string = core::stringify_args(args, false, Some(" "));

        unsafe {
            OUTPUT.extend(
                string
                    .split('\n')
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>(),
            )
        };
        Ok(MalType::Nil(()))
    }

    fn make_test_env() -> Env {
        let mut test_env = create_core_namespace();
        add_premade_lisp_fn_to(&mut test_env);
        test_env
    }

    #[test]
    fn step_3_eval_tester() {
        let file = include_str!("../tests/step3_env.mal");
        run_test(file, make_test_env(), false);
    }
    #[test]
    fn step_4_eval_tester() {
        let file = include_str!("../tests/step4_if_fn_do.mal");
        run_test(file, make_test_env(), false);
    }

    #[test]
    fn step_5_eval_tester() {
        let file = include_str!("../tests/step5_tco.mal");
        run_test(file, make_test_env(), false);
    }

    #[test]
    fn step_6_eval_tester() {
        let file = include_str!("../tests/step6_file.mal");
        run_test(file, make_test_env(), false);
    }

    #[test]
    fn step_7_eval_tester() {
        let file = include_str!("../tests/step7_quote.mal");
        run_test(file, make_test_env(), false);
    }

    #[test]
    fn step_8_eval_tester() {
        let file = include_str!("../tests/step8_macros.mal");
        run_test(file, make_test_env(), false);
    }

    #[test]
    fn step_9_eval_tester() {
        let file = include_str!("../tests/step9_try.mal");
        run_test(file, make_test_env(), false);
    }

    #[test]
    fn step_a_eval_tester() {
        let file = include_str!("../tests/stepA_mal.mal");
        run_test(file, make_test_env(), false);
    }

    fn run_test(file: &str, mut test_env: Env, print_line: bool) {
        let _ = test_env.set(
            &MalType::Symbol("prn".to_string()),
            MalType::LiftedFunc(
                "Simulate Print".to_string(),
                simulate_print,
                Box::new(MalType::Nil(())),
            ),
        );
        let _ = test_env.set(
            &MalType::Symbol("println".to_string()),
            MalType::LiftedFunc(
                "Simulate Println".to_string(),
                simulate_println,
                Box::new(MalType::Nil(())),
            ),
        );
        let _ = test_env.set(
            &MalType::Symbol("rust-eval".to_string()),
            MalType::LiftedFunc(
                "Rust Eval".to_string(),
                |_args| new_eval_error("Cannot evaluate within testing environment".to_string()),
                Box::new(MalType::Nil(())),
            ),
        );
        let mut result = Ok(MalType::Nil(()));
        let mut current_out_index = 0;
        for (number, line) in file.lines().enumerate().map(|(n, l)| (n + 1, l)) {
            if line.is_empty() || line.starts_with(";;") || line.starts_with(";>>>") {
                continue;
            } else if line.starts_with(";=>") {
                let output = line.trim_start_matches(";=>");
                if let Ok(ref success) = result {
                    assert_eq!(
                        printer::pr_str_old(success.clone(), true),
                        output,
                        "Checking line {number} evaluates correctly"
                    );
                } else {
                    panic!(
                        "Result not ok: got {result:?}; but should be: {output} (see line {number})"
                    );
                }
                assert!(&result.is_ok());
            } else if let Some(pat) = line.strip_prefix(";/") {
                match unsafe { OUTPUT.get(current_out_index) } {
                    Some(output) => {
                        let re = regex::Regex::new(pat).unwrap();
                        assert!(re.is_match(output), "See line {number} for error");
                    }
                    None => assert!(result.is_err(), "See line {number} for error"),
                };
                current_out_index += 1;
            } else {
                unsafe { OUTPUT.clear() };
                current_out_index = unsafe { OUTPUT.len() };
                result = eval(
                    *reader::read_str(line).expect("Invalid Input"),
                    test_env.clone(),
                );
            }
            if print_line {
                println!("Finished line {number}");
            }
        }
    }
}
