use std::collections::VecDeque;

use reader::{MalType, ParseError};
use rustyline::{error::ReadlineError, DefaultEditor};

use crate::step3_env::env::Env;

/// Either results in a MAL type or gives back a message for an error
pub type MalResult = Result<MalType, String>;

pub(crate) mod reader {

    use std::{collections::VecDeque, fmt::Display};

    use logos::Logos;

    use super::MalResult;

    #[derive(Logos, Clone, Debug, PartialEq)]
    #[logos(skip r"[ \t\n\f]+")]
    /// Token produced from the lexing step
    enum Token<'t> {
        #[token("(")]
        /// Open Parenthesis (
        OpenParen,
        #[token(")")]
        /// Close Parenthesis )
        CloseParen,
        #[token("[")]
        /// Open Bracket [
        OpenBracket,
        #[token("]")]
        /// Close Bracket ]
        CloseBracket,
        #[token("{")]
        /// Open Brace {
        OpenBrace,
        #[token("}")]
        /// Close Brace }
        CloseBrace,
        #[token("'")]
        /// Apostrophe '
        Quote,
        #[token("`")]
        /// Backtick `
        Quasiquote,
        #[token("~")]
        /// Tilde ~
        Unquote,
        #[token("@")]
        /// At-symbol @
        Deref,
        #[token("^")]
        /// Caret ^
        Meta,

        #[regex(r#""(?:\\.|[^\\"])*"?"#)]
        /// String: Open Quote ... Stuff in between ... Close Quote
        StringTok(&'t str),

        #[regex(r";.*")]
        /// Comment: Semicolon ... Stuff in between ... until \n
        Comment(&'t str),

        #[regex(r#"[^\s\[\]{}('"`,;~@)]*"#)]
        /// Atom: Anything else, should be catch all
        ///
        /// Note: Atom disallows ~ and @ because of Logos's parsing rule; this is not in original regex
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
        /// Check if a given token is a comment
        fn is_comment(&self) -> bool {
            matches!(self, Token::Comment(_))
        }
    }

    #[derive(PartialEq, Clone, Debug, PartialOrd)]
    /// Basic Types with in the interpreter
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
        Func(String, fn(VecDeque<MalType>) -> MalResult),
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
                MalType::Func(name, _) => f.write_str(&format!("Built-in Function: {}", &name)),
            }
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq)]
    #[non_exhaustive]
    /// Error messages produced during parsing stage
    pub enum ParseError {
        Eof,
        UnbalancedParen,
    }

    impl Display for ParseError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                ParseError::Eof | ParseError::UnbalancedParen => {
                    f.write_str("(EOF|end of input|unbalanced)")
                } // _ => todo!(),
            }
        }
    }

    /// Read from a string input and try to produce a new expression
    pub fn read_str(input: &str) -> Result<Box<MalType>, ParseError> {
        let mut lexed_tokens = tokenize(input);
        let (expr, _rem) = read_form(&mut lexed_tokens)?;
        Ok(Box::new(expr))
    }

    /// Take a string and produce a list of token
    fn tokenize<'t>(input: &'t str) -> VecDeque<Token<'t>> {
        Box::new(Token::lexer(input).filter_map(|res: Result<Token<'t>, ()>| res.ok()))
            .filter(|tok| !tok.is_comment())
            .collect()
    }

    /// Take a sequence of token and
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

    /// Read a meta
    ///
    /// Example: ^{"a" 1} [1 2 3] -> (with-meta [1 2 3] {"a" 1})
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

    ///
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

    /// Read in a vector from lexed list
    ///
    /// Example:  
    /// * \[1, 2, 3] -> **OK**: MalType::Vector(\[1,2,3])
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

    /// Read a hashmap from lexed list
    ///
    /// Example:
    /// * {"a" 1} -> **OK**: MalType::Map({"a":1}))
    /// * {"a" 1 -> **ERR**: Unbalanced Parenthesis
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

    ///Check if a given string is valid with the following condition:
    /// 1. Starts with a double quote mark
    /// 2. Ends with an unescaped double quote
    /// 3. Escaped characters allowed between
    fn check_string(s: &str) -> bool {
        s.chars().fold((true, false), |acc, c| match (c, acc) {
            ('\"', (quote_open, false)) => (!quote_open, false),
            ('\\', (quote_open, false)) => (quote_open, true),
            (_c, (quote_open, true)) => (quote_open, false),
            _ => acc,
        }) == (true, false)
    }

    /// Read an atom from the given lexed list, can be either string or atom
    ///
    ///
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
    use super::Ast;

    /// Print out the AST expression
    pub fn pr_str(ast: Ast) -> String {
        ast.expr.to_string()
    }
}

pub(crate) mod env {
    use std::collections::HashMap;

    use super::reader::MalType;

    #[derive(Debug, Clone)]
    pub struct Env {
        outer: Option<Box<Env>>,
        data: HashMap<String, MalType>,
    }

    impl Env {
        /// Create a new environment (with no outer environment)
        pub fn new() -> Self {
            Self {
                outer: None,
                data: HashMap::new(),
            }
        }

        /// Create a new environment with outer (parent) environment
        pub fn with_outer(outer: Box<Env>) -> Self {
            Self {
                outer: Some(outer),
                data: HashMap::new(),
            }
        }

        /// Takes a symbol key and a mal value, adds it to the environment
        pub fn set(&mut self, key: String, val: MalType) -> &mut Self {
            self.data.insert(key, val);
            self
        }

        /// Search the environment or its outer environment for a key
        pub fn find(&self, key: String) -> Option<&Self> {
            if self.data.contains_key(&key) {
                Some(self)
            } else if let Some(outer_env) = &self.outer {
                outer_env.find(key)
            } else {
                None
            }
        }

        /// Gets the value from the environment given a key or an error for it not being found
        pub fn get(&self, key: String) -> Result<MalType, String> {
            if let Some(env) = self.find(key.clone()) {
                Ok(env.data.get(&key).unwrap().clone())
            } else {
                Err(format!("'{key}' not found"))
            }
        }
    }
}
/// Abstract syntax tree
pub struct Ast {
    pub expr: MalType,
}

impl Ast {
    pub fn new(expr: MalType) -> Self {
        Self { expr }
    }
}

#[derive(Debug)]
/// Union of all the types of errors in the program
enum ReplError {
    Readline(ReadlineError),
    Parse(ParseError),
    Eval(String),
}

fn eval_error<T>(msg: &str) -> Result<T, ReplError> {
    Err(ReplError::Eval(msg.to_string()))
}

/// Read in from a given editor and parse it into an AST
fn read(rl: &mut DefaultEditor) -> Result<Ast, ReplError> {
    let line = rl.readline("user> ").map_err(ReplError::Readline)?;
    rl.add_history_entry(line.clone())
        .map_err(ReplError::Readline)?;
    let expr = *reader::read_str(&line).map_err(ReplError::Parse)?;
    Ok(Ast { expr })
}

/// Evaluate an expression with a given environment
fn eval_ast(expr: MalType, env: &mut Env) -> Result<MalType, ReplError> {
    match expr {
        MalType::Symbol(s) => env.get(s).map_err(ReplError::Eval),
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

/// Evaluate the given expression and return the result
fn eval(expr: MalType, env: &mut Env) -> Result<MalType, ReplError> {
    match expr {
        MalType::List(ref v) if v.is_empty() => Ok(expr),
        MalType::List(mut v) => {
            let Some(mal) = v.pop_front() else {
                return eval_error("Resulting list is empty and cannot be evaluated!");
            };

            match mal {
                MalType::Symbol(s) if s == "def!" => {
                    let Some(MalType::Symbol(key)) = v.pop_front() else {
                        return eval_error("No symbol to define");
                    };
                    let Some(val) = v.pop_front() else {
                        return eval_error("No value to bind to symbol");
                    };
                    let evaluated_val = eval(val, env)?;
                    env.set(key, evaluated_val.clone());
                    Ok(evaluated_val)
                }
                MalType::Symbol(s) if s == "let*" => {
                    let mut new_env = Env::with_outer(Box::new(env.clone()));
                    match v.pop_front() {
                        Some(MalType::List(binds)) => {
                            // Bind[even] = symbols
                            // Bind[odd] = values
                            for (key, val) in
                                binds.iter().step_by(2).zip(binds.iter().skip(1).step_by(2))
                            {
                                match key {
                                    MalType::Symbol(sym) => {
                                        let evaluated_val = eval(val.clone(), &mut new_env)?;
                                        new_env.set(sym.to_owned(), evaluated_val);
                                    }
                                    _ => {
                                        return eval_error(&format!(
                                            "Binding to non-symbol: {}",
                                            key
                                        ))
                                    }
                                }
                            }
                            let Some(key) = v.pop_front() else {
                                return eval_error("Second argument empty");
                            };
                            eval(key, &mut new_env)
                        }
                        Some(MalType::Vector(binds)) => {
                            // Bind[even] = symbols
                            // Bind[odd] = values
                            for (key, val) in
                                binds.iter().step_by(2).zip(binds.iter().skip(1).step_by(2))
                            {
                                match key {
                                    MalType::Symbol(sym) => {
                                        let evaluated_val = eval(val.clone(), &mut new_env)?;
                                        new_env.set(sym.to_owned(), evaluated_val);
                                    }
                                    _ => {
                                        return eval_error(&format!(
                                            "Binding to non-symbol: {}",
                                            key
                                        ))
                                    }
                                }
                            }
                            let Some(key) = v.pop_front() else {
                                return eval_error("Second argument empty");
                            };
                            eval(key, &mut new_env)
                        }
                        Some(_) => eval_error("Non-list binding found for let*"),
                        None => eval_error("No values to bind in environment"),
                    }
                }
                _ => match eval_ast(mal, env)? {
                    MalType::Func(_, func) => {
                        let args = v.into_iter().map(|val| eval(val, env)).try_fold(
                            VecDeque::new(),
                            |mut args, a| match a {
                                Ok(val) => {
                                    args.push_back(val);
                                    Ok(args)
                                }
                                Err(err) => Err(err),
                            },
                        )?;
                        func(args).map_err(ReplError::Eval)
                    }
                    non_func => eval_error(&format!("Couldn't apply from result of {}", non_func)),
                },
            }
        }
        _ => eval_ast(expr, env),
    }
}

/// Print a given AST
fn print(value: Ast) {
    println!("{}", printer::pr_str(value))
}

macro_rules! env_set {
    ($repl_env:ident, $op:expr => $fn:expr) => {
        $repl_env.set($op.to_string(), MalType::Func($op.to_string(), $fn));
    };
}

fn create_default_environment() -> Env {
    let mut env = Env::new();

    env_set!(env, "+" => |args| match (&args[0], &args[1]) {
        (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x + y)),
        _ => Err("Add function does not work on non-number types".to_string()),
    });
    env_set!(env, "-" => |args| match (&args[0], &args[1]) {
        (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x - y)),
        _ => Err("Sub function does not work on non-number types".to_string()),
    });
    env_set!(env, "*" => |args| match (&args[0], &args[1]) {
        (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x * y)),
        _ => Err("Mul function does not work on non-number types".to_string()),
    });
    env_set!(env, "/" => |args| match (&args[0], &args[1]) {
        (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number(x / y)),
        _ => Err("Div function does not work on non-number types".to_string()),
    });
    env
}

/// Runs the read, evaluate, and print functions in that order
fn rep(rl: &mut DefaultEditor, env: &mut Env) -> Result<(), ReplError> {
    let ast = read(rl)?;
    let res = Ast::new(eval(ast.expr, env)?);
    print(res);
    Ok(())
}

/// Runs the repl
pub fn main() -> rustyline::Result<()> {
    let mut rl = DefaultEditor::new()?;
    let mut repl_env = create_default_environment();
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

    // #[test_case(&[ r#"(+ 1 2)"#, r#"(/ (- (+ 5 (* 2 3)) 3) 4)"# ], &[ Ok(r#"3"#), Ok(r#"2"#) ] ; r#"Testing REPL_ENV"#)]
    // #[test_case(&[ r#"(def! x 3)"#, r#"x"#, r#"(def! x 4)"#, r#"x"#, r#"(def! y (+ 1 7))"#, r#"y"# ], &[ Ok(r#"3"#), Ok(r#"3"#), Ok(r#"4"#), Ok(r#"4"#), Ok(r#"8"#), Ok(r#"8"#) ] ; r#"Testing def!"#)]
    // #[test_case(&[ r#"(def! mynum 111)"#, r#"(def! MYNUM 222)"#, r#"mynum"#, r#"MYNUM"# ], &[ Ok(r#"111"#), Ok(r#"222"#), Ok(r#"111"#), Ok(r#"222"#) ] ; r#"Verifying symbols are case-sensitive"#)]
    // #[test_case(&[ r#"(abc 1 2 3)"#, r#"(def! w 123)\n(def! w (abc))\nw"# ], &[ Err(r#"*\'?abc\'? not found.*"#), Ok(r#"123"#) ] ; r#"Check that error aborts def!"#)]
    // #[test_case(&[ r#"(def! a 4)"#, r#"(let* (q 9) q)"#, r#"(let* (q 9) a)"#, r#"(let* (z 2) (let* (q 9) a))"# ], &[ Ok(r#"4"#), Ok(r#"9"#), Ok(r#"4"#), Ok(r#"4"#) ] ; r#"Testing outer environment"#)]
    // #[test_case(&[ r#"(let* [z 9] z)"#, r#"(let* [p (+ 2 3) q (+ 2 p)] (+ p q))"# ], &[ Ok(r#"9"#), Ok(r#"12"#) ] ; r#"Testing let* with vector bindings"#)]
    // #[test_case(&[ r#"(let* (a 5 b 6) [3 4 a [b 7] 8])"# ], &[ Ok(r#"[3 4 5 [6 7] 8]"#) ] ; r#"Testing vector evaluation"#)]
    // /// Test for successful evaluation
    // #[test_case(&[ r#"(let* (z 9) z)"#, r#"(let* (x 9) x)"#, r#"x"#, r#"(let* (z (+ 2 3)) (+ 1 z))"#, r#"(let* (p (+ 2 3) q (+ 2 p)) (+ p q))"#, r#"(def! y (let* (z 7) z))\ny"# ], &[ Ok(r#"9"#), Ok(r#"9"#), Ok(r#"4"#), Ok(r#"6"#), Ok(r#"12"#), Ok(r#"7"#) ] ; r#"Testing let*"#)]
    #[test]
    fn step_3_eval_tester() {
        let file = include_str!("../tests/step3_env.mal");
        let mut test_env = create_default_environment();
        let mut result = Ok(MalType::Nil);
        for line in file.lines() {
            if line.is_empty() || line.starts_with(";;") || line.starts_with(";>>>") {
                continue;
            } else if line.starts_with(";=>") {
                let output = line.trim_start_matches(";=>");
                if let Ok(success) = &result {
                    assert_eq!(success.to_string(), output);
                } else {
                    panic!("Result not ok: {:?}; but should be: {output}", result);
                }
                assert!(&result.is_ok());
                // assert_eq!(result.unwrap().to_string(), line.trim_start_matches(";=>"));
            } else if line.starts_with(";/") {
                assert!(result.is_err());
            } else {
                result = eval(
                    *reader::read_str(line).expect("Invalid Input"),
                    &mut test_env,
                );
            }
        }
        // for (input, output) in inputs.iter().zip(outputs) {
        //     let result = eval(
        //         *reader::read_str(input).expect("Invalid Input"),
        //         &mut test_env,
        //     );
        //     if let Ok(success) = result {
        //         assert!(output.is_ok());
        //         assert_eq!(success.to_string(), output.unwrap());
        //     } else {
        //         assert!(output.is_err());
        //     }
        // }
    }
}
