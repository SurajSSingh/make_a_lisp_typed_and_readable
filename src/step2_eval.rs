use std::collections::{HashMap, VecDeque};

use reader::{MalType, ParseError};
use rustyline::{error::ReadlineError, DefaultEditor};

pub type MalResult = Result<MalType, String>;

pub(crate) mod reader {
    use std::{collections::VecDeque, fmt::Display};

    use logos::Logos;

    use super::MalResult;

    #[derive(Logos, Clone, Debug, PartialEq)]
    #[logos(skip r"[ \t\n\f]+")]
    enum Token<'t> {
        #[token("(")]
        OpenParen,
        #[token(")")]
        CloseParen,
        #[token("[")]
        OpenBracket,
        #[token("]")]
        CloseBracket,
        #[token("{")]
        OpenBrace,
        #[token("}")]
        CloseBrace,
        #[token("'")]
        Quote,
        #[token("`")]
        Quasiquote,
        #[token("~")]
        Unquote,
        #[token("@")]
        Deref,
        #[token("^")]
        Meta,

        // #[regex(r"[\[\]{}()'`~^@]")]
        // SingleTok(&'t str),
        #[regex(r#""(?:\\.|[^\\"])*"?"#)]
        StringTok(&'t str),

        #[regex(r";.*")]
        Comment(&'t str),

        #[regex(r#"[^\s\[\]{}('"`,;~@)]*"#)]
        Atom(&'t str),
    }

    impl<'t> Display for Token<'t> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Token::StringTok(str) => f.write_str(str),
                Token::Comment(com) => f.write_str(com),
                Token::Atom(atm) => f.write_str(atm),
                Token::Quote => f.write_str("'"),
                Token::Quasiquote => f.write_str("`"),
                Token::Unquote => f.write_str("~"),
                Token::OpenParen => f.write_str("("),
                Token::CloseParen => f.write_str(")"),
                Token::OpenBracket => f.write_str("["),
                Token::CloseBracket => f.write_str("]"),
                Token::OpenBrace => f.write_str("{"),
                Token::CloseBrace => f.write_str("}"),
                Token::Deref => f.write_str("@"),
                Token::Meta => f.write_str("^"),
            }
        }
    }

    impl<'t> Token<'t> {
        fn is_atom(&self) -> bool {
            matches!(self, Token::Atom(_))
        }
        fn is_comment(&self) -> bool {
            matches!(self, Token::Comment(_))
        }
    }

    #[derive(PartialEq, Clone, Debug, PartialOrd)]
    pub enum MalType {
        Nil,
        True,
        False,
        Quote(Box<MalType>),
        Quasiquote(Box<MalType>),
        Unquote(Box<MalType>),
        SpliceUnquote(Box<MalType>),
        Deref(Box<MalType>),
        Meta(Vec<MalType>),
        Number(f64),
        Keyword(String),
        Symbol(String),
        String(String),
        List(VecDeque<MalType>),
        Vector(Vec<MalType>),
        Map(Vec<(MalType, MalType)>),
        BuiltInFunc(String, fn(VecDeque<MalType>) -> MalResult),
    }

    impl Display for MalType {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                MalType::Quote(q) => f.write_str(&format!("(quote {q})")),
                MalType::Unquote(q) => f.write_str(&format!("(unquote {q})")),
                MalType::Quasiquote(q) => f.write_str(&format!("(quasiquote {q})")),
                MalType::SpliceUnquote(q) => f.write_str(&format!("(splice-unquote {q})")),
                MalType::Deref(d) => f.write_str(&format!("(deref {d})")),
                MalType::Number(n) => f.write_str(&n.to_string()),
                MalType::Keyword(k) => f.write_str(k),
                MalType::Symbol(s) => f.write_str(s),
                MalType::Nil => f.write_str("nil"),
                MalType::True => f.write_str("true"),
                MalType::False => f.write_str("false"),
                MalType::String(s) => f.write_str(s),
                MalType::Meta(m) => f.write_str(&format!(
                    "(with-meta {})",
                    m.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                MalType::List(l) => f.write_str(&format!(
                    "({})",
                    l.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                MalType::Vector(v) => f.write_str(&format!(
                    "[{}]",
                    v.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                MalType::Map(m) => f.write_str(&format!(
                    "{{{}}}",
                    m.iter()
                        .map(|(k, v)| format!("{} {}", k, v))
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                MalType::BuiltInFunc(name, _) => {
                    f.write_str(&format!("Built-in Function: {}", &name))
                }
            }
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq)]
    #[non_exhaustive]
    pub enum ParseError {
        Eof,
        UnbalancedParen,
    }

    impl Display for ParseError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                ParseError::Eof | ParseError::UnbalancedParen => {
                    f.write_str("(EOF|end of input|unbalanced)")
                }
                _ => todo!(),
            }
        }
    }

    pub fn read_str(input: &str) -> Result<Box<MalType>, ParseError> {
        let mut lexed_tokens = tokenize(input);
        let (expr, _rem) = read_form(&mut lexed_tokens)?;
        Ok(Box::new(expr))
    }
    fn tokenize<'t>(input: &'t str) -> VecDeque<Token<'t>> {
        Box::new(Token::lexer(input).filter_map(|res: Result<Token<'t>, ()>| res.ok()))
            .filter(|tok| !tok.is_comment())
            // .map(|tok| tok.to_string())
            .collect()
    }

    fn read_form<'t>(
        lex_list: &'t mut VecDeque<Token<'t>>,
    ) -> Result<(MalType, &'t mut VecDeque<Token<'t>>), ParseError> {
        if let Some(token) = lex_list.get(0) {
            match token {
                Token::OpenParen => {
                    lex_list.pop_front();
                    Ok(read_list(lex_list)?)
                }
                Token::OpenBracket => {
                    lex_list.pop_front();
                    Ok(read_vector(lex_list)?)
                }
                Token::OpenBrace => {
                    lex_list.pop_front();
                    Ok(read_hashmap(lex_list)?)
                }
                Token::Quote => {
                    lex_list.pop_front();
                    let (form, remaining) = read_form(lex_list)?;
                    Ok((MalType::Quote(Box::new(form)), remaining))
                }
                Token::Quasiquote => {
                    lex_list.pop_front();
                    let (form, remaining) = read_form(lex_list)?;
                    Ok((MalType::Quasiquote(Box::new(form)), remaining))
                }
                Token::Deref => {
                    lex_list.pop_front();
                    let (form, remaining) = read_form(lex_list)?;
                    Ok((MalType::Deref(Box::new(form)), remaining))
                }
                Token::Meta => {
                    lex_list.pop_front();
                    Ok(read_meta(lex_list)?)
                }
                Token::Unquote => {
                    lex_list.pop_front();
                    if let Some(token2) = lex_list.get(0) {
                        if matches!(token2, Token::Deref) {
                            lex_list.pop_front();
                            let (form, remaining) = read_form(lex_list)?;
                            Ok((MalType::SpliceUnquote(Box::new(form)), remaining))
                        } else {
                            let (form, remaining) = read_form(lex_list)?;
                            Ok((MalType::Unquote(Box::new(form)), remaining))
                        }
                    } else {
                        Err(ParseError::Eof)
                    }
                }
                _ => Ok(read_atom(lex_list)?),
            }
        } else {
            Err(ParseError::Eof)
        }
    }

    fn read_meta<'t>(
        lex_list: &'t mut VecDeque<Token<'t>>,
    ) -> Result<(MalType, &'t mut VecDeque<Token<'t>>), ParseError> {
        let mut list = Vec::new();
        let mut rem = lex_list;
        while rem.get(0).is_some() {
            let (result, remaining) = read_form(rem)?;
            list.push(result);
            rem = remaining;
        }
        list.reverse();
        Ok((MalType::Meta(list), rem))
    }

    fn read_list<'t>(
        lex_list: &'t mut VecDeque<Token<'t>>,
    ) -> Result<(MalType, &'t mut VecDeque<Token<'t>>), ParseError> {
        let mut list = VecDeque::new();
        let mut rem = lex_list;
        while let Some(token) = rem.get(0) {
            match token {
                Token::CloseParen => {
                    rem.pop_front();
                    return Ok((MalType::List(list), rem));
                }
                _ => {
                    let (result, remaining) = read_form(rem)?;
                    list.push_back(result);
                    rem = remaining;
                }
            }
        }
        Err(ParseError::UnbalancedParen)
    }

    fn read_vector<'t>(
        lex_list: &'t mut VecDeque<Token<'t>>,
    ) -> Result<(MalType, &'t mut VecDeque<Token<'t>>), ParseError> {
        let mut list = Vec::new();
        let mut rem = lex_list;
        while let Some(token) = rem.get(0) {
            match token {
                Token::CloseBracket => {
                    rem.pop_front();
                    return Ok((MalType::Vector(list), rem));
                }
                _ => {
                    let (result, remaining) = read_form(rem)?;
                    list.push(result);
                    rem = remaining;
                }
            }
        }
        Err(ParseError::UnbalancedParen)
    }
    fn read_hashmap<'t>(
        lex_list: &'t mut VecDeque<Token<'t>>,
    ) -> Result<(MalType, &'t mut VecDeque<Token<'t>>), ParseError> {
        let mut map = Vec::new();
        let mut rem = lex_list;
        while let Some(token) = rem.get(0) {
            match token {
                Token::CloseBrace => {
                    rem.pop_front();
                    return Ok((MalType::Map(map), rem));
                }
                _ => {
                    let (key, remaining_first) = read_form(rem)?;
                    let (value, remaining_second) = read_form(remaining_first)?;
                    map.push((key, value));
                    rem = remaining_second;
                }
            }
        }
        Err(ParseError::UnbalancedParen)
    }

    fn check_string(s: &str) -> bool {
        s.chars().fold((true, false), |acc, c| match (c, acc) {
            ('\"', (quote_open, false)) => (!quote_open, false),
            ('\\', (quote_open, false)) => (quote_open, true),
            (_c, (quote_open, true)) => (quote_open, false),
            _ => acc,
        }) == (true, false)
    }

    fn read_atom<'t>(
        lex_list: &'t mut VecDeque<Token<'t>>,
    ) -> Result<(MalType, &'t mut VecDeque<Token<'t>>), ParseError> {
        if let Some(token) = lex_list.pop_front() {
            match token {
                Token::StringTok(string) => {
                    if string.len() > 1 && string.ends_with('\"') && check_string(string) {
                        Ok((MalType::String(string.to_string()), lex_list))
                    } else {
                        Err(ParseError::UnbalancedParen)
                    }
                }
                Token::Atom(atom) => {
                    if let Ok(num) = atom.parse::<f64>() {
                        Ok((MalType::Number(num), lex_list))
                    } else {
                        match atom {
                            "nil" => Ok((MalType::Nil, lex_list)),
                            "true" => Ok((MalType::True, lex_list)),
                            "false" => Ok((MalType::False, lex_list)),
                            c if c.starts_with(':') => {
                                Ok((MalType::Keyword(atom.to_string()), lex_list))
                            }
                            _ => Ok((MalType::Symbol(atom.to_string()), lex_list)),
                        }
                    }
                }
                _ => unreachable!(),
            }
        } else {
            Err(ParseError::Eof)
        }
    }
}

pub(crate) mod printer {
    use crate::step2_eval::Ast;

    pub fn pr_str(ast: Ast) -> String {
        ast.expr.to_string()
    }
}

pub struct Ast {
    pub expr: MalType,
}

impl Ast {
    pub fn new(expr: MalType) -> Self {
        Self { expr }
    }
}

#[derive(Debug)]
enum ReplError {
    Readline(ReadlineError),
    Parse(ParseError),
    Eval(String),
}

fn read(rl: &mut DefaultEditor) -> Result<Ast, ReplError> {
    let line = rl.readline("user> ").map_err(ReplError::Readline)?;
    rl.add_history_entry(line.clone())
        .map_err(ReplError::Readline)?;
    let expr = *reader::read_str(&line).map_err(ReplError::Parse)?;
    Ok(Ast { expr })
}

fn eval_ast(expr: MalType, env: &mut HashMap<String, MalType>) -> Result<MalType, ReplError> {
    match expr {
        MalType::Symbol(s) => {
            if let Some(mal) = env.get(&s) {
                Ok(mal.clone())
            } else {
                Err(ReplError::Eval(format!("Symbol {} not found", s)))
            }
        }
        MalType::List(l) => {
            let new_list =
                l.iter()
                    .map(|e| eval(e.clone(), env))
                    .try_fold(VecDeque::new(), |mut list, r| {
                        if let Ok(e) = r {
                            list.push_back(e);
                            Ok(list)
                        } else {
                            Err(r.unwrap_err())
                        }
                    });
            new_list.map(MalType::List)
        }
        MalType::Vector(v) => {
            let new_vec =
                v.iter()
                    .map(|e| eval(e.clone(), env))
                    .try_fold(Vec::new(), |mut vector, r| {
                        if let Ok(e) = r {
                            vector.push(e);
                            Ok(vector)
                        } else {
                            Err(r.unwrap_err())
                        }
                    });
            new_vec.map(MalType::Vector)
        }
        MalType::Map(m) => {
            let new_map = m.iter().map(|(k, v)| (k, eval(v.clone(), env))).try_fold(
                Vec::new(),
                |mut map, (k, r)| {
                    if let Ok(e) = r {
                        map.push((k.to_owned(), e));
                        Ok(map)
                    } else {
                        Err(r.unwrap_err())
                    }
                },
            );
            new_map.map(MalType::Map)
        }
        _ => Ok(expr),
    }
}

fn eval(expr: MalType, env: &mut HashMap<String, MalType>) -> Result<MalType, ReplError> {
    match expr {
        MalType::List(ref v) if v.is_empty() => Ok(expr),
        MalType::List(ref v) => {
            let new_list = eval_ast(expr, env)?;
            if let MalType::List(mut v) = new_list {
                if let Some(mal) = v.pop_front() {
                    match mal {
                        MalType::BuiltInFunc(_, func) => func(v).map_err(ReplError::Eval),
                        _ => unreachable!("Unapplicable Type: Not a function"),
                    }
                } else {
                    Err(ReplError::Eval(
                        "Resulting list is empty and cannot be evaluated!".to_string(),
                    ))
                }
            } else {
                Err(ReplError::Eval(
                    "Resulting list could not be evaluated!".to_string(),
                ))
            }
        }
        _ => eval_ast(expr, env),
    }
}

fn print(value: Ast) {
    println!("{}", printer::pr_str(value))
}

macro_rules! built_in_insert {
    ($repl_env:ident, $op:expr => $fn:expr) => {
        $repl_env.insert($op.to_string(), MalType::BuiltInFunc($op.to_string(), $fn));
    };
}

fn rep(rl: &mut DefaultEditor, env: &mut HashMap<String, MalType>) -> Result<(), ReplError> {
    let ast = read(rl)?;
    let res = Ast::new(eval(ast.expr, env)?);
    Ok(print(res))
}

pub fn main() -> rustyline::Result<()> {
    let mut rl = DefaultEditor::new()?;
    let mut repl_env: HashMap<String, MalType> = HashMap::default();
    built_in_insert!(repl_env, "+" => |args| match (&args[0], &args[1]) {
        (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x + y)),
        _ => Err("Add function does not work on non-number types".to_string()),
    });
    built_in_insert!(repl_env, "-" => |args| match (&args[0], &args[1]) {
        (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x - y)),
        _ => Err("Sub function does not work on non-number types".to_string()),
    });
    built_in_insert!(repl_env, "*" => |args| match (&args[0], &args[1]) {
        (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x * y)),
        _ => Err("Mul function does not work on non-number types".to_string()),
    });
    built_in_insert!(repl_env, "/" => |args| match (&args[0], &args[1]) {
        (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x / y)),
        _ => Err("Div function does not work on non-number types".to_string()),
    });
    loop {
        if let Err(err) = rep(&mut rl, &mut repl_env) {
            match err {
                ReplError::Readline(ReadlineError::Eof | ReadlineError::Interrupted) => break,
                ReplError::Readline(err) => {
                    println!("{}", err);
                    break;
                }
                ReplError::Parse(ParseError::UnbalancedParen) => {
                    println!("Unbalanced Paren");
                }
                ReplError::Eval(err) => {
                    println!("Eval Error: {}", err);
                }
                _ => {
                    println!("Unknown ");
                    break;
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_case::test_case;

    fn create_test_environment() -> HashMap<String, MalType> {
        let mut test_evn = HashMap::default();
        built_in_insert!(test_evn, "+" => |args| match (&args[0], &args[1]) {
            (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x + y)),
            _ => Err("Add function does not work on non-number types".to_string()),
        });
        built_in_insert!(test_evn, "-" => |args| match (&args[0], &args[1]) {
            (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x - y)),
            _ => Err("Sub function does not work on non-number types".to_string()),
        });
        built_in_insert!(test_evn, "*" => |args| match (&args[0], &args[1]) {
            (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x * y)),
            _ => Err("Mul function does not work on non-number types".to_string()),
        });
        built_in_insert!(test_evn, "/" => |args| match (&args[0], &args[1]) {
            (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x / y)),
            _ => Err("Div function does not work on non-number types".to_string()),
        });
        test_evn
    }

    #[test_case(r#"(+ 1 2)"#, r#"3"# ; r#"Testing evaluation of arithmetic operations"#)]
    #[test_case(r#"(+ 5 (* 2 3))"#, r#"11"# ; r#"Test 1: (+ 5 (* 2 3)) => 11"#)]
    #[test_case(r#"(- (+ 5 (* 2 3)) 3)"#, r#"8"# ; r#"Test 2: (- (+ 5 (* 2 3)) 3) => 8"#)]
    #[test_case(r#"(/ (- (+ 5 (* 2 3)) 3) 4)"#, r#"2"# ; r#"Test 3: (/ (- (+ 5 (* 2 3)) 3) 4) => 2"#)]
    #[test_case(r#"(/ (- (+ 515 (* 87 311)) 302) 27)"#, r#"1010"# ; r#"Test 4: (/ (- (+ 515 (* 87 311)) 302) 27) => 1010"#)]
    #[test_case(r#"(* -3 6)"#, r#"-18"# ; r#"Test 5: (* -3 6) => -18"#)]
    #[test_case(r#"(/ (- (+ 515 (* -87 311)) 296) 27)"#, r#"-994"# ; r#"Test 6: (/ (- (+ 515 (* -87 311)) 296) 27) => -994"#)]
    #[test_case(r#"()"#, r#"()"# ; r#"Testing empty list"#)]
    #[test_case(r#"[1 2 (+ 1 2)]"#, r#"[1 2 3]"# ; r#"Testing evaluation within collection literals"#)]
    #[test_case(r#"{"a" (+ 7 8)}"#, r#"{"a" 15}"# ; r#"Test 8: {"a" (+ 7 8)} => {"a" 15}"#)]
    #[test_case(r#"{:a (+ 7 8)}"#, r#"{:a 15}"# ; r#"Test 9: {:a (+ 7 8)} => {:a 15}"#)]
    #[test_case(r#"[]"#, r#"[]"# ; r#"Check that evaluation hasn't broken empty collections"#)]
    #[test_case(r#"{}"#, r#"{}"# ; r#"Test 10: {} => {}"#)]
    fn step_2_tester_eval_success(input: &str, output: &str) {
        let result = eval(
            *reader::read_str(input).expect("Invalid Input"),
            &mut create_test_environment(),
        );
        assert!(result.is_ok());
        assert_eq!(result.unwrap().to_string(), output);
    }
    #[test_case(r#"(abc 1 2 3)"#, r#""# ; r#"Test 7: (abc 1 2 3) => "#)]
    fn step_2_tester_eval_failure(input: &str, error: &str) {
        let result = eval(
            *reader::read_str(input).expect("Invalid Input"),
            &mut create_test_environment(),
        );
        assert!(result.is_err());
        // assert_eq!(result.unwrap_err(), error);
    }
}
