#![deny(missing_docs)]
///! This is an attempt to improve the implementation of MalType, currently not working and incomplete
use std::{collections::VecDeque, fmt::Display};

use reader::{MalType, ParseError};
use rustyline::{error::ReadlineError, DefaultEditor};

use env::Env;

/// Either results in a MAL type or gives back a message for an error
pub type MalResult = Result<MalType, String>;

pub(crate) mod reader {

    use std::{
        collections::{HashMap, VecDeque},
        fmt::Display,
    };

    use logos::{Logos, Span};

    use super::env::Env;

    #[derive(Debug, Clone, PartialEq, PartialOrd, Hash)]
    pub struct MyQueue<T>(usize, Vec<T>);

    impl<T> From<Vec<T>> for MyQueue<T> {
        fn from(value: Vec<T>) -> Self {
            Self(0, value)
        }
    }

    impl<T> From<VecDeque<T>> for MyQueue<T> {
        fn from(value: VecDeque<T>) -> Self {
            Self(0, value.into())
        }
    }

    impl<T> MyQueue<T> {
        pub fn new() -> Self {
            Self(0, Vec::new())
        }

        pub fn with_capacity(capacity: usize) -> Self {
            Self(0, Vec::with_capacity(capacity))
        }

        pub fn is_empty(&self) -> bool {
            self.0 >= self.1.len()
        }

        // No Push

        pub fn peek(&self) -> Option<&T> {
            self.1.first()
        }

        pub fn pop(&mut self) -> Option<&T> {
            self.0 += 1;
            self.1.get(self.0 - 1)
        }
    }

    #[derive(Logos, Clone, Debug, PartialEq, PartialOrd)]
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

    impl<'t> Token<'t> {
        /// Check if a given token is a comment
        fn is_comment(&self) -> bool {
            matches!(self, Token::Comment(_))
        }

        fn is_atom_with_name(&self, name: &str) -> bool {
            match self {
                Token::Atom(sym) if *sym == name => todo!(),
                _ => false,
            }
        }
    }

    #[derive(Debug, Clone, PartialEq, PartialOrd)]
    pub enum MalAtomic<S> {
        Nil,
        True,
        False,
        Number(f64),
        Keyword(String),
        String(String),
        Symbol(String),
    }

    impl Display for MalAtomic {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                MalAtomic::Nil => f.write_str("nil"),
                MalAtomic::True => f.write_str("true"),
                MalAtomic::False => f.write_str("false"),
                MalAtomic::Number(n) => f.write_str(&n.to_string()),
                MalAtomic::Keyword(s) | MalAtomic::String(s) | MalAtomic::Symbol(s) => {
                    f.write_str(s)
                }
            }
        }
    }

    #[derive(Debug, Clone)]
    pub enum MalComposite {
        List(MyQueue<MalType>),
        Vector(MyQueue<MalType>),
        HashMap(HashMap<String, MalType>),
    }

    impl Display for MalComposite {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                MalComposite::List(list) => f.write_fmt(format_args!(
                    "({})",
                    list.1
                        .into_iter()
                        .skip(list.0)
                        .map(|m| m.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                MalComposite::Vector(vec) => f.write_fmt(format_args!(
                    "[{}]",
                    vec.1
                        .into_iter()
                        .skip(vec.0)
                        .map(|m| m.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                MalComposite::HashMap(map) => f.write_fmt(format_args!(
                    "[{}]",
                    map.into_iter()
                        .map(|(k, v)| format!("{k} {v}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
            }
        }
    }

    #[derive(Debug, Clone)]
    pub enum MalFunction {
        Lifted(String),
        UserDefined {
            args: MyQueue<String>,
            body: MyQueue<MalType>,
            cenv: Env,
        },
    }

    impl Display for MalFunction {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                MalFunction::Lifted(name) => f.write_fmt(format_args!("Built-in<{name}>")),
                MalFunction::UserDefined { args, body, cenv } => f.write_str("#<function>"),
            }
        }
    }

    #[derive(Debug, Clone)]
    pub enum SpecialForm {
        Quote(Box<MalType>),
        Quasiquote(Box<MalType>),
        Unquote(Box<MalType>),
        SpliceUnquote(Box<MalType>),
        Deref(Box<MalType>),
        Meta(MyQueue<MalType>),
        Def(String, Box<MalType>),
        Let {
            bindings: MyQueue<(String, MalType)>,
            body: Box<MalType>,
        },
        Do(MyQueue<MalType>),
        If {
            condition: Box<MalType>,
            true_case: Box<MalType>,
            false_case: Option<Box<MalType>>,
        },
        Fn {
            args: MyQueue<String>,
            body: Box<MalType>,
            cenv: Env,
        },
    }

    impl Display for SpecialForm {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                SpecialForm::Quote(q) => f.write_fmt(format_args!("(quote {q})")),
                SpecialForm::Quasiquote(q) => f.write_fmt(format_args!("(quasiquote {q})")),
                SpecialForm::Unquote(q) => f.write_fmt(format_args!("(unquote {q})")),
                SpecialForm::SpliceUnquote(q) => f.write_fmt(format_args!("(splice-unquote {q})")),
                SpecialForm::Deref(d) => f.write_fmt(format_args!("(deref {d})")),
                SpecialForm::Meta(m) => f.write_fmt(format_args!(
                    "(with-meta {})",
                    m.1.iter()
                        .skip(m.0)
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                SpecialForm::Def(sym, val) => f.write_fmt(format_args!("(def! {sym} {val})")),
                SpecialForm::Let { bindings, body } => todo!(),
                SpecialForm::Do(d) => f.write_fmt(format_args!(
                    "(do {})",
                    d.1.iter()
                        .skip(d.0)
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                SpecialForm::If {
                    condition,
                    true_case,
                    false_case,
                } => {
                    if let Some(given_false_case) = false_case {
                        f.write_fmt(format_args!(
                            "(if {condition} {true_case} {given_false_case})"
                        ))
                    } else {
                        f.write_fmt(format_args!("(if {condition} {true_case})"))
                    }
                }
                SpecialForm::Fn { args, body, cenv } => f.write_fmt(format_args!(
                    "(fn* {} {body})",
                    args.1
                        .iter()
                        .skip(args.0)
                        .map(|a| a.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
            }
        }
    }

    #[derive(Clone, Debug)]
    /// Basic Types with in the interpreter
    pub enum MalType<S = ()> {
        Atomic(MalAtomic, S),
        Composite(MalComposite, S),
        Function(MalFunction, S),
        Special(SpecialForm, S),
    }

    impl Display for MalType {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.fmt(f)
        }
    }

    pub type SpannedMalType = MalType<Span>;

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
    pub fn read_str(input: &str) -> Result<Box<SpannedMalType>, ParseError> {
        let mut lexed_tokens = tokenize(input);
        let (expr, _rem) = read_form(&mut lexed_tokens)?;
        Ok(Box::new(expr))
    }

    type TokenQueue<'t> = MyQueue<(Token<'t>, Span)>;

    /// Take a string and produce a list of token
    fn tokenize<'t>(input: &'t str) -> TokenQueue<'t> {
        Token::lexer(input)
            .spanned()
            .filter(|tok| tok.0.is_ok())
            .map(|(res, span)| (res.unwrap(), span))
            .filter(|tok| !tok.0.is_comment())
            .collect::<Vec<_>>()
            .into()
    }

    /// Take a sequence of token and read its form
    fn read_form<'t>(
        lex_queue: &'t mut TokenQueue<'t>,
    ) -> Result<(SpannedMalType, &'t mut TokenQueue<'t>), ParseError> {
        if let Some((token, span)) = lex_queue.pop() {
            match token {
                Token::OpenParen => Ok(read_list(lex_queue)?),
                Token::OpenBracket => Ok(read_vector(lex_queue)?),
                Token::OpenBrace => Ok(read_hashmap(lex_queue)?),
                Token::Quote => {
                    let (form, remaining) = read_form(lex_queue)?;
                    Ok((MalType::Quote(Box::new(form)), remaining))
                }
                Token::Quasiquote => {
                    let (form, remaining) = read_form(lex_queue)?;
                    Ok((MalType::Quasiquote(Box::new(form)), remaining))
                }
                Token::Deref => {
                    let (form, remaining) = read_form(lex_queue)?;
                    Ok((MalType::Deref(Box::new(form)), remaining))
                }
                Token::Meta => Ok(read_meta(lex_queue)?),
                Token::Unquote => {
                    if let Some(token2) = lex_queue.get(0) {
                        if matches!(token2, Token::Deref) {
                            lex_queue.pop_front();
                            let (form, remaining) = read_form(lex_queue)?;
                            Ok((MalType::SpliceUnquote(Box::new(form)), remaining))
                        } else {
                            let (form, remaining) = read_form(lex_queue)?;
                            Ok((MalType::Unquote(Box::new(form)), remaining))
                        }
                    } else {
                        Err(ParseError::Eof)
                    }
                }
                _ => Ok((read_this_atom(token, span)?, lex_queue)),
            }
        } else {
            Err(ParseError::Eof)
        }
    }

    /// Read a meta
    ///
    /// Example: ^{"a" 1} [1 2 3] -> (with-meta [1 2 3] {"a" 1})
    fn read_meta<'t>(
        lex_queue: &'t mut TokenQueue<'t>,
    ) -> Result<(SpannedMalType, &'t mut TokenQueue<'t>), ParseError> {
        let mut list = Vec::new();
        let mut rem = lex_queue;
        let mut start = usize::max_value();
        let mut end = 0;
        while rem.peek().is_some() {
            let (result, remaining) = read_form(rem)?;
            list.push(result.0);
            start = result.1.start.min(start);
            end = result.1.end.max(end);
            rem = remaining;
        }
        list.reverse();
        Ok((
            SpannedMalType(
                MalType::Special(SpecialForm::Meta(MyQueue::from(list))),
                start..end,
            ),
            rem,
        ))
    }

    ///
    fn read_list<'t>(
        lex_queue: &'t mut TokenQueue<'t>,
    ) -> Result<(SpannedMalType, &'t mut TokenQueue<'t>), ParseError> {
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
        lex_queue: &'t mut TokenQueue<'t>,
    ) -> Result<(SpannedMalType, &'t mut TokenQueue<'t>), ParseError> {
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
        lex_queue: &'t mut TokenQueue<'t>,
    ) -> Result<(SpannedMalType, &'t mut TokenQueue<'t>), ParseError> {
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

    /// Read a specific atom
    ///
    /// Used when already popped atom from queue
    fn read_this_atom<'t>(token: &Token<'t>, span: &Span) -> Result<SpannedMalType, ParseError> {}

    /// Read an atom from the given lexed list, can be either string, special keyword, or symbol
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
                            "def!" => Ok((MalType::SpecialForm(SpecialKeyword::Def), lex_list)),
                            "let*" => Ok((MalType::SpecialForm(SpecialKeyword::Let), lex_list)),
                            "do" => Ok((MalType::SpecialForm(SpecialKeyword::Do), lex_list)),
                            "if" => Ok((MalType::SpecialForm(SpecialKeyword::If), lex_list)),
                            "fn*" => Ok((MalType::SpecialForm(SpecialKeyword::Fn), lex_list)),
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
    use std::{collections::HashMap, fmt::Display};

    use super::reader::MalType;

    #[derive(Debug, Clone)]
    pub struct Env {
        outer: Option<Box<Env>>,
        data: HashMap<String, MalType>,
    }

    impl Display for Env {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("Env")
        }
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

        /// Create a new environment to associate bindings with exprs
        pub fn update_bindings(&mut self, binds: Vec<String>, exprs: Vec<MalType>) -> &mut Self {
            self.data.extend(binds.into_iter().zip(exprs.into_iter()));
            self
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

impl Display for ReplError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReplError::Readline(r) => r.fmt(f),
            ReplError::Parse(p) => p.fmt(f),
            ReplError::Eval(e) => f.write_str(e),
        }
    }
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
            dbg!(&mal);
            match mal {
                MalType::SpecialForm(SpecialKeyword::Def) => {
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
                MalType::SpecialForm(SpecialKeyword::Let) => {
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
                MalType::SpecialForm(SpecialKeyword::Do) => {
                    if let MalType::List(l) = eval_ast(MalType::List(v), env)? {
                        Ok(l.into_iter().last().unwrap_or(MalType::Nil))
                    } else {
                        eval_error("Do form invalid")
                    }
                }
                MalType::SpecialForm(SpecialKeyword::If) => {
                    let Some(condition) = v.pop_front() else {
                        return eval_error("If form has no condition");
                    };
                    if matches!(eval_ast(condition, env)?, MalType::Nil | MalType::False) {
                        v.pop_front();
                        eval(v.pop_front().unwrap_or(MalType::Nil), env)
                    } else {
                        let Some(true_case) = v.pop_front() else {
                            return eval_error("If form has no true case");
                        };
                        eval(true_case, env)
                    }
                }
                MalType::SpecialForm(SpecialKeyword::Fn) => {
                    dbg!(&v);
                    let Some(MalType::List(bindings)) = v.pop_front() else {
                        return  eval_error("Function has no bindings");
                    };
                    let Some(body) = v.pop_front() else {
                        return  eval_error("Function has no body");
                    };
                    Ok(MalType::Func {
                        name: String::from("#<function>"),
                        args: bindings
                            .into_iter()
                            .map(|m| {
                                if let MalType::Symbol(s) = m {
                                    Ok(s)
                                } else {
                                    eval_error(&format!("Not a symbol: {:?}", m))
                                }
                            })
                            .try_fold(Vec::new(), |mut vec, a| {
                                if let Ok(s) = a {
                                    vec.push(s);
                                    Ok(vec)
                                } else {
                                    Err(a.unwrap_err())
                                }
                            })?,
                        body: Box::new(body),
                        clo_env: Env::with_outer(Box::new(env.clone())),
                    })
                }
                _ => match eval_ast(mal, env)? {
                    MalType::BuiltInFunc(_, func) => func(v, env).map_err(ReplError::Eval),
                    MalType::Func {
                        args,
                        body,
                        mut clo_env,
                        ..
                    } => {
                        let applied_env = clo_env.update_bindings(args, v.into());
                        dbg!(&applied_env);
                        eval(*body, applied_env)
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

macro_rules! env_set_op {
    ($op:path, $name:expr, $sym:expr => $repl_env:ident) => {
        $repl_env.set(
            $sym.to_string(),
            MalType::BuiltInFunc(stringify!($op).to_string(), |params, env| {
                if params.len() < 2 {
                    return Err("Not enough arguments for ".to_string() + $name);
                }
                match (&params[0], &params[1]) {
                    (MalType::Number(x), MalType::Number(y)) => Ok(MalType::Number($op(x, y))),
                    (s1 @ MalType::Symbol(_), b) => {
                        if let Ok(MalType::Number(x)) = eval(s1.clone(), env) {
                            match b {
                                MalType::Number(y) => Ok(MalType::Number($op(x, y))),
                                s2 @ MalType::Symbol(_) => {
                                    if let Ok(MalType::Number(y)) = eval(s2.clone(), env) {
                                        Ok(MalType::Number($op(x, y)))
                                    } else {
                                        Err(format!("Symbol not a number: {:?}", s2))
                                    }
                                }
                                _ => Err($name.to_string()
                                    + " function does not work on non-number types"),
                            }
                        } else {
                            Err(format!("Symbol not a number: {:?}", s1))
                        }
                    }
                    _ => Err($name.to_string() + " function does not work on non-number types"),
                }
            }),
        );
    };
}

/// Creates a new environment with basic 4 function arithmetic operations
fn create_default_environment() -> Env {
    let mut env = Env::new();
    env_set_op!(std::ops::Add::add, "Addition", "+" => env);
    env_set_op!(std::ops::Sub::sub, "Subtract", "-" => env);
    env_set_op!(std::ops::Mul::mul, "Multiply", "*" => env);
    env_set_op!(std::ops::Div::div, "Divide",   "/" => env);
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

    #[test]
    fn step_3_eval_tester() {
        let file = include_str!("../tests/step4_if_fn_do.mal");
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
    }
}
