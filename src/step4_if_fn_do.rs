#![deny(missing_docs)]
use std::collections::VecDeque;

use reader::{MalType, ParseError};
use rustyline::{error::ReadlineError, DefaultEditor};

use env::Env;

use self::{core::create_core_environment, reader::SpecialKeyword};

/// Either results in a MAL type or gives back a message for an error
pub type MalResult = Result<MalType, String>;

pub(crate) mod reader {

    use std::{collections::VecDeque, fmt::Display};

    use logos::Logos;

    use super::{env::Env, MalResult};

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

    #[derive(Debug, Clone, Copy, PartialEq)]
    pub enum SpecialKeyword {
        Def,
        Let,
        Do,
        If,
        Fn,
    }

    impl Display for SpecialKeyword {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                SpecialKeyword::Def => f.write_str("def!"),
                SpecialKeyword::Let => f.write_str("let*"),
                SpecialKeyword::Do => f.write_str("do"),
                SpecialKeyword::If => f.write_str("if"),
                SpecialKeyword::Fn => f.write_str("fn"),
            }
        }
    }

    #[derive(Clone)]
    /// Basic Types with in the interpreter
    pub enum MalType {
        Nil(()),
        Bool(bool),
        Quote(Box<MalType>),
        Quasiquote(Box<MalType>),
        Unquote(Box<MalType>),
        SpliceUnquote(Box<MalType>),
        Deref(Box<MalType>),
        Meta(Vec<MalType>),
        Number(f64),
        Keyword(String),
        /// Holds any special symbols
        SpecialForm(SpecialKeyword),
        Symbol(String),
        String(String),
        List(VecDeque<MalType>),
        Vector(Vec<MalType>),
        Map(Vec<(MalType, MalType)>),
        LiftedFunc(String, fn(VecDeque<MalType>, &mut Env) -> MalResult),
        UserFunc(Vec<String>, Box<MalType>, Env),
    }

    impl PartialEq for MalType {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (Self::Nil(l0), Self::Nil(r0)) => l0 == r0,
                (Self::Bool(l0), Self::Bool(r0)) => l0 == r0,
                (Self::Quote(l0), Self::Quote(r0)) => l0 == r0,
                (Self::Quasiquote(l0), Self::Quasiquote(r0)) => l0 == r0,
                (Self::Unquote(l0), Self::Unquote(r0)) => l0 == r0,
                (Self::SpliceUnquote(l0), Self::SpliceUnquote(r0)) => l0 == r0,
                (Self::Deref(l0), Self::Deref(r0)) => l0 == r0,
                (Self::Meta(l0), Self::Meta(r0)) => l0 == r0,
                (Self::Number(l0), Self::Number(r0)) => l0 == r0,
                (Self::Keyword(l0), Self::Keyword(r0)) => l0 == r0,
                (Self::SpecialForm(l0), Self::SpecialForm(r0)) => l0 == r0,
                (Self::Symbol(l0), Self::Symbol(r0)) => l0 == r0,
                (Self::String(l0), Self::String(r0)) => l0 == r0,
                (Self::List(l0), Self::List(r0)) => l0 == r0,
                (Self::Vector(l0), Self::Vector(r0)) => l0 == r0,
                (Self::Map(l0), Self::Map(r0)) => l0 == r0,
                (Self::LiftedFunc(l0, l1), Self::LiftedFunc(r0, r1)) => l0 == r0,
                (Self::UserFunc(l0, l1, l2), Self::UserFunc(r0, r1, r2)) => {
                    l0 == r0 && l1 == r1 && l2 == r2
                }
                _ => false,
            }
        }
    }

    impl std::fmt::Debug for MalType {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Nil(()) => write!(f, "Nil"),
                MalType::Bool(arg0) => f.debug_tuple("Bool").field(arg0).finish(),
                Self::Quote(arg0) => f.debug_tuple("Quote").field(arg0).finish(),
                Self::Quasiquote(arg0) => f.debug_tuple("Quasiquote").field(arg0).finish(),
                Self::Unquote(arg0) => f.debug_tuple("Unquote").field(arg0).finish(),
                Self::SpliceUnquote(arg0) => f.debug_tuple("SpliceUnquote").field(arg0).finish(),
                Self::Deref(arg0) => f.debug_tuple("Deref").field(arg0).finish(),
                Self::Meta(arg0) => f.debug_tuple("Meta").field(arg0).finish(),
                Self::Number(arg0) => f.debug_tuple("Number").field(arg0).finish(),
                Self::Keyword(arg0) => f.debug_tuple("Keyword").field(arg0).finish(),
                Self::SpecialForm(arg0) => f.debug_tuple("SpecialForm").field(arg0).finish(),
                Self::Symbol(arg0) => f.debug_tuple("Symbol").field(arg0).finish(),
                Self::String(arg0) => f.debug_tuple("String").field(arg0).finish(),
                Self::List(arg0) => f.debug_tuple("List").field(arg0).finish(),
                Self::Vector(arg0) => f.debug_tuple("Vector").field(arg0).finish(),
                Self::Map(arg0) => f.debug_tuple("Map").field(arg0).finish(),
                Self::LiftedFunc(arg0, _arg1) => f.debug_tuple("LiftedFunc").field(arg0).finish(),
                Self::UserFunc(arg0, arg1, arg2) => f
                    .debug_tuple("UserFunc")
                    .field(arg0)
                    .field(arg1)
                    .field(arg2)
                    .finish(),
            }
        }
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
                MalType::Nil(()) => f.write_str("nil"),
                MalType::Bool(b) => f.write_fmt(format_args!("{b}")),
                MalType::String(s) => f.write_str(s),
                MalType::SpecialForm(word) => f.write_str(&word.to_string()),
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
                MalType::LiftedFunc(name, _) => {
                    f.write_str(&format!("Built-in Function: {}", &name))
                }
                MalType::UserFunc(_params, _body, _env) => f.write_str("#<function>"),
            }
        }
    }
    impl MalType {
        /// Returns `true` if the mal type is [`UserFunc`].
        ///
        /// [`UserFunc`]: MalType::UserFunc
        #[must_use]
        pub fn is_user_func(&self) -> bool {
            matches!(self, Self::UserFunc(..))
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
                }
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

    /// Take a sequence of token and read its form
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

    /// Read a list
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
                            "nil" => Ok((MalType::Nil(()), lex_list)),
                            "true" => Ok((MalType::Bool(true), lex_list)),
                            "false" => Ok((MalType::Bool(false), lex_list)),
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
    use std::collections::HashMap;

    use super::reader::MalType;

    #[derive(Debug, Clone, PartialEq)]
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

        /// Create a new environment with outer (parent) environment and bindings (parameters to expressions)
        pub fn with_outer_and_bindings(
            outer: Box<Env>,
            binds: Vec<String>,
            exprs: Vec<MalType>,
        ) -> Self {
            Self {
                outer: Some(outer),
                data: binds.into_iter().zip(exprs).collect(),
            }
        }

        /// Create a new environment with outer (parent) environment and bindings (parameters to expressions).
        /// Data will also includes items not already found in outer environment.
        pub fn intersection_bindings(
            outer: Box<Env>,
            other: &Env,
            binds: Vec<String>,
            exprs: Vec<MalType>,
        ) -> Self {
            Self {
                outer: Some(outer.clone()),
                data: other
                    .data
                    .iter()
                    // Skip over anything found in outer environment
                    .filter(|(k, _)| !outer.data.contains_key(&(*k).clone()))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .chain(binds.into_iter().zip(exprs))
                    .collect(),
            }
        }

        /// Takes a symbol key and a mal value, adds it to the environment
        pub fn set(&mut self, key: String, val: MalType) -> &mut Self {
            self.data.insert(key, val);
            self
        }

        pub fn set_symbol(&mut self, key: MalType, val: MalType) -> &mut Self {
            match key {
                MalType::Symbol(s) => self.set(s, val),
                _ => self,
            }
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

        pub fn find_symbol(&self, key: MalType) -> Option<&Self> {
            match key {
                MalType::Symbol(s) => self.find(s),
                _ => None,
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

        pub fn get_symbol(&self, key: MalType) -> Result<MalType, String> {
            match key {
                MalType::Symbol(s) => self.get(s),
                _ => Err("Not a symbol".to_string()),
            }
        }
    }
}

pub(crate) mod core {
    use std::collections::VecDeque;

    use super::{env::Env, print, reader::MalType, Ast, MalResult};

    pub fn prn(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        if let Some(expr) = args.get(0) {
            print(Ast::new(expr.clone()))
        };
        Ok(MalType::Nil(()))
    }

    pub fn to_list(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        Ok(MalType::List(args))
    }

    pub fn is_list(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        match args.get(0) {
            Some(MalType::List(_)) => Ok(MalType::Bool(true)),
            Some(_) => Ok(MalType::Bool(false)),
            None => Err("Not enough arguments".to_string()),
        }
    }

    pub fn is_empty(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        match args.get(0) {
            Some(MalType::List(l)) => Ok(MalType::Bool(l.is_empty())),
            Some(MalType::Vector(v)) => Ok(MalType::Bool(v.is_empty())),
            Some(MalType::Map(m)) => Ok(MalType::Bool(m.is_empty())),
            Some(_) => Err("Is emptyonly works only with non-atomics types".to_string()),
            None => Err("Not enough arguments".to_string()),
        }
    }

    pub fn count(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        match args.get(0) {
            Some(MalType::List(l)) => Ok(MalType::Number(l.len() as f64)),
            Some(MalType::Vector(v)) => Ok(MalType::Number(v.len() as f64)),
            Some(MalType::Map(m)) => Ok(MalType::Number(m.len() as f64)),
            Some(MalType::Nil(_)) => Ok(MalType::Number(0.0)),
            Some(_) => Err("Count only works only with non-atomics types and nil".to_string()),
            None => Err("Not enough arguments".to_string()),
        }
    }

    macro_rules! set_lift_op {
        // Unary operator
        ($repl_env:ident add $sym:expr, $func:path : $in_t1: path => $out_type:path) => {
            $repl_env.set(
                $sym.to_string(),
                MalType::LiftedFunc(stringify!($func).to_string(), |args, env| {
                    let func_name = stringify!($func).split("::").last().unwrap();
                    if args.len() < 1 {
                        return Err(format!("Not enough arguments for {func_name}"));
                    }
                    match &args[0] {
                        $in_t1(x) => Ok($out_type($func(x))),
                        MalType::Symbol(s) => match env.get(s) {
                            $in_t1(x) => Ok($out_type($func(x))),
                            _ => Err(format!(
                                "func_name} function does not work for given types."
                            )),
                        },
                        _ => Err(format!(
                            "func_name} function does not work for given types."
                        )),
                    }
                }),
            )
        };
        // Binary operator - non default
        ($repl_env:ident += $sym:expr, $func:path : $($in_t1: path, $in_t2: path)|+ => $out_type:path) => {
            $repl_env.set(
                $sym.to_string(),
                MalType::LiftedFunc(stringify!($func).to_string(), |args, env| {
                    let func_name = stringify!($func).split("::").last().unwrap();
                    if args.len() < 2 {
                        return Err(format!("Not enough arguments for {func_name}"));
                    }
                    match (&args[0], &args[1]) {
                        $(($in_t1(x), $in_t2(y)) => Ok($out_type($func(x, y)))),+,
                        $((MalType::Symbol(s1), $in_t2(y)) => match env.get(s1.to_string()) {
                            Ok($in_t1(x)) => Ok($out_type($func(&x, y))),
                            Ok(_) => Err(format!(
                                "{func_name} function does not work for given types."
                            )),
                            Err(err) => Err(err),
                        }),+
                        $(($in_t1(x), MalType::Symbol(s2)) => match env.get(s2.to_string()) {
                            Ok($in_t2(y)) => Ok($out_type($func(x, &y))),
                            Ok(_) => Err(format!(
                                "{func_name} function does not work for given types."
                            )),
                            Err(err) => Err(err),
                        }),+
                        (MalType::Symbol(s1), MalType::Symbol(s2)) => match env.get(s1.to_string()) {
                            $(Ok($in_t1(x)) => match env.get(s2.to_string()){
                                Ok($in_t2(y)) =>Ok($out_type($func(&x, &y))),
                                Ok(_) => Err(format!(
                                    "{func_name} function does not work for given types."
                                )),
                                Err(err) => Err(err),
                            }),+
                            Ok(_) => Err(format!(
                                "{func_name} function does not work for given types."
                            )),
                            Err(err) => Err(err),
                        }
                        _ => Err(format!(
                            "{func_name} function does not work for given types."
                        )),
                    }
                }),
            )
        };
        // Binary operator - default
        ($repl_env:ident += $sym:expr, $func:path : any => $out_type:path) => {
            $repl_env.set(
                $sym.to_string(),
                MalType::LiftedFunc(stringify!($func).to_string(), |args, _env| {
                    let func_name = stringify!($func).split("::").last().unwrap();
                    if args.len() < 2 {
                        return Err(format!("Not enough arguments for {func_name}"));
                    }
                    Ok($out_type($func(&args[0], &args[1])))
                }),
            )
        };
    }

    macro_rules! set_core_fn {
        ($repl_env:ident += $func:ident as $name:expr , $pretty_name:expr) => {
            $repl_env.set(
                $name.to_string(),
                MalType::LiftedFunc($pretty_name.to_string(), $func),
            );
        };
        ($repl_env:ident += $func:ident as $name:expr) => {
            $repl_env.set(
                $name.to_string(),
                MalType::LiftedFunc(stringify!($func).to_string(), $func),
            );
        };
        ($repl_env:ident += $func:ident , $pretty_name:expr) => {
            $repl_env.set(
                stringify!($func).to_string(),
                MalType::LiftedFunc($pretty_name.to_string(), $func),
            );
        };
        ($repl_env:ident += $func:ident) => {
            $repl_env.set(
                stringify!($func).to_string(),
                MalType::LiftedFunc(stringify!($func).to_string(), $func),
            );
        };
    }

    /// Creates a new environment with basic 4 function arithmetic operations
    pub fn create_core_environment() -> Env {
        let mut env = Env::new();
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
        set_core_fn!(env += prn, "print");
        set_core_fn!(env += to_list as "list", "make list");
        set_core_fn!(env += is_list as "list?");
        set_core_fn!(env += is_empty as "empty?");
        set_core_fn!(env += count);

        env
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
fn eval(ast: MalType, env: &mut Env) -> Result<MalType, ReplError> {
    match ast.clone() {
        MalType::List(ref v) if v.is_empty() => Ok(ast),
        MalType::List(mut ast_expr) => {
            let Some(mal) = ast_expr.pop_front() else {
                return eval_error("Resulting list is empty and cannot be evaluated!");
            };

            match mal {
                MalType::SpecialForm(SpecialKeyword::Def) => {
                    let Some(MalType::Symbol(key)) = ast_expr.pop_front() else {
                        return eval_error("No symbol to define");
                    };
                    let Some(val) = ast_expr.pop_front() else {
                        return eval_error("No value to bind to symbol");
                    };
                    let evaluated_val = eval(val, env)?;
                    env.set(key, evaluated_val.clone());
                    // env.set(key.clone(), evaluated_val.clone());
                    // // Special case for user functions
                    // // If recursive, it shoud have a reference to itself in environment
                    // if evaluated_val.is_user_func() {
                    //     // Extract user function
                    //     if let MalType::UserFunc(params, body, _) =
                    //         env.get(key.clone()).map_err(ReplError::Eval)?
                    //     {
                    //         // Re-add user function with updated environment
                    //         env.set(key, MalType::UserFunc(params, body, env.clone()));
                    //     }
                    // }
                    Ok(evaluated_val)
                }
                MalType::SpecialForm(SpecialKeyword::Let) => {
                    let mut new_env = Env::with_outer(Box::new(env.clone()));
                    match ast_expr.pop_front() {
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
                            let Some(key) = ast_expr.pop_front() else {
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
                            let Some(key) = ast_expr.pop_front() else {
                                return eval_error("Second argument empty");
                            };
                            eval(key, &mut new_env)
                        }
                        Some(_) => eval_error("Non-list binding found for let*"),
                        None => eval_error("No values to bind in environment"),
                    }
                }
                MalType::SpecialForm(SpecialKeyword::Do) => {
                    match eval_ast(MalType::List(ast_expr), env)? {
                        MalType::List(l) => Ok(l
                            .back()
                            .map(|last| last.to_owned())
                            .unwrap_or(MalType::Nil(()))),
                        _ => eval_error("Expected list"),
                    }
                }
                MalType::SpecialForm(SpecialKeyword::If) => {
                    let Some(cond) = ast_expr.pop_front() else {
                        return eval_error("No condition for if form given");
                    };
                    match eval(cond, env) {
                        Ok(MalType::Nil(()) | MalType::Bool(false)) => {
                            ast_expr.pop_front();
                            eval(ast_expr.pop_front().unwrap_or(MalType::Nil(())), env)
                        }
                        Ok(_) => {
                            if let Some(true_branch) = ast_expr.pop_front() {
                                eval(true_branch, env)
                            } else {
                                eval_error("No true branch to evaluate")
                            }
                        }
                        Err(_) => eval_error("Failed to evaluate condition"),
                    }
                }
                MalType::SpecialForm(SpecialKeyword::Fn) => {
                    let params = match ast_expr.pop_front() {
                        Some(MalType::List(l)) => {
                            l.into_iter().try_fold(Vec::new(), |mut acc, m| {
                                if let MalType::Symbol(s) = m {
                                    acc.push(s);
                                    Ok(acc)
                                } else {
                                    eval_error(&format!("Not a symbol: {:?}", m))
                                }
                            })?
                        }
                        Some(MalType::Vector(v)) => {
                            v.into_iter().try_fold(Vec::new(), |mut acc, m| {
                                if let MalType::Symbol(s) = m {
                                    acc.push(s);
                                    Ok(acc)
                                } else {
                                    eval_error(&format!("Not a symbol: {:?}", m))
                                }
                            })?
                        }
                        _ => return eval_error("No parameter list found"),
                    };
                    let Some(body) = ast_expr.pop_front() else {
                        return eval_error("Function body not defined");
                    };
                    Ok(MalType::UserFunc(params, Box::new(body), env.clone()))
                }
                _ => match eval_ast(ast, env)? {
                    MalType::List(mut list) => {
                        let Some(func) = list.pop_front() else {
                            return eval_error("Function not defined");
                        };
                        match func {
                            MalType::LiftedFunc(_, func) => {
                                func(list, env).map_err(ReplError::Eval)
                            }
                            MalType::UserFunc(params, body, outer_env) => {
                                let mut fn_env = Env::intersection_bindings(
                                    Box::new(outer_env),
                                    env,
                                    params,
                                    list.into(),
                                );
                                eval(*body, &mut fn_env)
                            }
                            non_func => eval_error(&format!("Expected a function, got {non_func}")),
                        }
                    }
                    non_list => eval_error(&format!("Expected a list, got {non_list}")),
                },
            }
        }
        _ => eval_ast(ast, env),
    }
}

/// Print a given AST
fn print(value: Ast) {
    println!("{}", printer::pr_str(value))
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
    let mut repl_env = create_core_environment();
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
    use super::{core::create_core_environment, *};
    static mut OUTPUT: Vec<String> = vec![];

    pub fn simulate_print(args: VecDeque<MalType>, _env: &mut Env) -> Result<MalType, String> {
        match args.get(0) {
            Some(expr) => {
                unsafe { OUTPUT.push(expr.to_string()) };
                Ok(MalType::Nil(()))
            }
            None => Err("Not enough arguments".to_string()),
        }
    }

    #[test]
    fn step_4_eval_tester() {
        let file = include_str!("../tests/step4_if_fn_do.mal");
        let mut test_env = create_core_environment();
        test_env.set(
            "prn".to_string(),
            MalType::LiftedFunc("Simulate Print".to_string(), simulate_print),
        );
        let mut result = Ok(MalType::Nil(()));
        let mut current_out_index = 0;
        for (number, line) in file.lines().enumerate() {
            if line.is_empty() || line.starts_with(";;") || line.starts_with(";>>>") {
                continue;
            } else if line.starts_with(";=>") {
                let output = line.trim_start_matches(";=>");
                if let Ok(success) = &result {
                    assert_eq!(
                        success.to_string(),
                        output,
                        "Checking line {number} evaluates correctly"
                    );
                } else {
                    panic!(
                        "Result not ok: got {result:?}; but should be: {output} (see line {number})"
                    );
                }
                assert!(&result.is_ok());
                // assert_eq!(result.unwrap().to_string(), line.trim_start_matches(";=>"));
            } else if line.starts_with(";/") {
                match unsafe { OUTPUT.get(current_out_index) } {
                    Some(output) => {
                        assert!(line.contains(output), "See line {number} for error");
                    }
                    None => assert!(result.is_err(), "See line {number} for error"),
                }
                current_out_index += 1;
            } else {
                unsafe { OUTPUT.clear() };
                current_out_index = unsafe { OUTPUT.len() };
                result = eval(
                    *reader::read_str(line).expect("Invalid Input"),
                    &mut test_env,
                );
            }
        }
    }
}
