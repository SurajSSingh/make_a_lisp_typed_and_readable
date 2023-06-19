#![deny(missing_docs)]
use std::collections::VecDeque;

use reader::{MalType, ParseError};
use rustyline::{error::ReadlineError, DefaultEditor};

use env::Env;

use self::{
    core::{add_premade_lisp_fn_to, create_core_environment},
    reader::SpecialKeyword,
};

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
        List(Vec<MalType>),
        Vector(Vec<MalType>),
        Map(Vec<(MalType, MalType)>),
        LiftedFunc(String, fn(Vec<MalType>) -> MalResult),
        MalFunc {
            fn_ast: Box<MalType>,
            params: Vec<String>,
            fn_env: Env,
            fn_val: Box<MalType>,
        },
    }

    impl PartialEq for MalType {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                // Default cases
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
                (Self::LiftedFunc(l0, _l1), Self::LiftedFunc(r0, _r1)) => l0 == r0,
                (
                    Self::MalFunc {
                        fn_ast: _ast0,
                        params: _p0,
                        fn_env: _env0,
                        fn_val: _fn0,
                    },
                    Self::MalFunc {
                        fn_ast: _ast1,
                        params: _p1,
                        fn_env: _env1,
                        fn_val: _fn1,
                    },
                ) => {
                    // FIXME: Currently, no two mal functions are the same
                    false
                }
                // Special case: Equal length List and Vector
                (Self::List(lst), Self::Vector(vec)) | (Self::Vector(vec), Self::List(lst))
                    if lst.len() == vec.len() =>
                {
                    lst.iter().zip(vec.iter()).all(|(l, r)| l == r)
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
                Self::MalFunc {
                    fn_ast,
                    params,
                    fn_env,
                    fn_val,
                } => f
                    .debug_struct("MalFunc")
                    .field("fn_ast", fn_ast)
                    .field("params", params)
                    .field("fn_env", fn_env)
                    .field("fn_val", fn_val)
                    .finish(),
            }
        }
    }

    impl Display for MalType {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str(&super::printer::pr_str(self.clone(), true))
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
        let mut list = Vec::new();
        let mut rem = lex_list;
        while let Some(token) = rem.get(0) {
            match token {
                Token::CloseParen => {
                    rem.pop_front();
                    return Ok((MalType::List(list), rem));
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
                        Ok((
                            MalType::String(
                                string[1..string.len() - 1]
                                    .chars()
                                    .fold(
                                        (String::new(), false),
                                        |(mut str, previous_backslash), ch| match (
                                            ch,
                                            previous_backslash,
                                        ) {
                                            // Escape newline
                                            ('n', true) => {
                                                str.push('\n');
                                                (str, false)
                                            }
                                            // Escape quote
                                            ('"', true) => {
                                                str.push('\"');
                                                (str, false)
                                            }
                                            ('\\', true) => {
                                                str.push('\\');
                                                (str, false)
                                            }
                                            // Default escaped character
                                            (c, true) => {
                                                str.push('\\');
                                                str.push(c);
                                                (str, false)
                                            }
                                            // Start escaping
                                            ('\\', false) => (str, true),
                                            // Unescaped character
                                            (c, false) => {
                                                str.push(c);
                                                (str, false)
                                            }
                                        },
                                    )
                                    .0,
                            ),
                            lex_list,
                        ))
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
            MalType::Quote(q) => format!("(quote {}", pr_str(*q, print_readably)),
            MalType::Quasiquote(q) => format!("(quasiquote {}", pr_str(*q, print_readably)),
            MalType::Unquote(u) => format!("(unquote {}", pr_str(*u, print_readably)),
            MalType::SpliceUnquote(s) => format!("(splice-quote {}", pr_str(*s, print_readably)),
            MalType::Deref(d) => format!("(deref {}", pr_str(*d, print_readably)),
            MalType::Meta(m) => format!(
                "(with-meta {}",
                m.into_iter()
                    .map(|t| pr_str(t, print_readably))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            MalType::Number(n) => n.to_string(),
            MalType::Keyword(k) => k,
            MalType::SpecialForm(k) => k.to_string(),
            MalType::Symbol(s) => s,
            MalType::List(l) => format!(
                "({})",
                l.into_iter()
                    .map(|m| pr_str(m, print_readably))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            MalType::Vector(v) => format!(
                "[{}]",
                v.into_iter()
                    .map(|m| pr_str(m, print_readably))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            MalType::Map(m) => format!(
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
            MalType::LiftedFunc(n, _) => format!("Built-in Function: {n}"),
            MalType::MalFunc {
                fn_ast,
                params,
                fn_env: _,
                fn_val: _,
            } => format!("(fn* ({}) {fn_ast})", params.join(" ")),
        }
    }
}

pub(crate) mod env {
    use std::{cell::RefCell, collections::HashMap, rc::Rc};

    use super::{new_eval_error, reader::MalType, ReplError};

    // Adapted from https://github.com/kanaka/mal/blob/master/impls/rust/env.rs

    #[derive(Debug, Clone, PartialEq, Default)]
    pub struct EnvStruct {
        outer: Option<Env>,
        data: RefCell<HashMap<String, MalType>>,
    }

    #[derive(Debug, Clone, PartialEq, Default)]
    pub struct Env(Rc<EnvStruct>);

    impl Env {
        pub fn new(outer: Option<Env>) -> Self {
            Env(Rc::new(EnvStruct {
                data: RefCell::new(HashMap::default()),
                outer,
            }))
        }
        pub fn with_bindings(
            outer: Option<Env>,
            binds: &[String],
            exprs: &[MalType],
        ) -> Result<Env, ReplError> {
            let mut env = Env::new(outer);

            let mut variadic_start = None;
            for (i, b) in binds.iter().enumerate() {
                if b == "&" {
                    variadic_start = Some(i + 1);
                    break;
                }
                match exprs.get(i) {
                    Some(e) => env.set(&MalType::Symbol(b.to_string()), e.clone())?,
                    None => {
                        return new_eval_error(String::from(
                            "Not enough arguments to the function",
                        ));
                    }
                };
            }
            if let Some(start) = variadic_start {
                let Some(key) = binds.get(start).map(|s|MalType::Symbol(s.to_string())) else {
                    return new_eval_error(String::from(
                        "No name found for variadic arguments",
                    ));
                };
                let val = exprs
                    .get((start - 1)..)
                    .map_or(MalType::Nil(()), |args| MalType::List(args.to_vec()));
                env.set(&key, val)?;
            }
            Ok(env)
        }
        pub fn find(&self, key: &str) -> Option<Env> {
            match (self.0.data.borrow().contains_key(key), self.0.outer.clone()) {
                (true, _) => Some(self.clone()),
                (false, Some(outer)) => outer.find(key),
                _ => None,
            }
        }
        pub fn get(&self, key: &MalType) -> Result<MalType, ReplError> {
            let MalType::Symbol(sym) = key else {
                return new_eval_error(format!("The key is not a symbol: got {}", key));
            };
            let Some(env) = self.find(sym) else {
                return new_eval_error(format!("Could not find the key: {}", sym));
            };
            let val = env
                .0
                .data
                .borrow()
                .get(sym)
                .cloned()
                .ok_or(ReplError::Eval(format!("Could not find the key: {}", sym)))?;
            Ok(val)
        }

        /// Set a key in the environment to a value.
        pub fn set(&mut self, key: &MalType, val: MalType) -> Result<MalType, ReplError> {
            let MalType::Symbol(sym) = key else {
                return new_eval_error(format!("The key is not a symbol: got {}", key));
            };
            self.0
                .data
                .try_borrow_mut()
                .map(|mut map| map.insert(sym.clone(), val.clone()))
                .map_err(|_| ReplError::Eval("Could not access environment".to_string()))?;
            Ok(val)
        }
    }
}

pub(crate) mod core {
    use super::{env::Env, printer::pr_str, reader::MalType, rep, MalResult};

    /// Apply pr_str to each argument and join them together
    pub fn stringify_args(
        args: Vec<MalType>,
        print_readably: bool,
        join_str: Option<&str>,
    ) -> String {
        args.into_iter()
            .map(|a| pr_str(a, print_readably))
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
        Ok(MalType::List(args))
    }

    /// Check if first argument is a list
    pub fn is_list(args: Vec<MalType>) -> MalResult {
        match args.get(0) {
            Some(MalType::List(_)) => Ok(MalType::Bool(true)),
            Some(_) => Ok(MalType::Bool(false)),
            None => Err("Not enough arguments".to_string()),
        }
    }

    /// Check if first argument is empty
    pub fn is_empty(args: Vec<MalType>) -> MalResult {
        match args.get(0) {
            Some(MalType::List(l)) => Ok(MalType::Bool(l.is_empty())),
            Some(MalType::Vector(v)) => Ok(MalType::Bool(v.is_empty())),
            Some(MalType::Map(m)) => Ok(MalType::Bool(m.is_empty())),
            Some(_) => Err("Is emptyonly works only with non-atomics types".to_string()),
            None => Err("Not enough arguments".to_string()),
        }
    }

    /// Check the number of elements in first argument
    pub fn count(args: Vec<MalType>) -> MalResult {
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
                        [_, _, ..] => Err(format!(
                            "{func_name} function does not work for given type."
                        )),
                        [] | [_] => Err(format!("Not enough arguments for {func_name}")),
                    }
                }),
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
                        [] | [_] => Err(format!("Not enough arguments for {func_name}")),
                    }
                }),
            ).expect("Macro did not set core function properly")
        };
    }

    macro_rules! set_core_fn {
        ($repl_env:ident += $func:ident as $name:expr , $pretty_name:expr) => {
            $repl_env
                .set(
                    &MalType::Symbol($name.to_string()),
                    MalType::LiftedFunc($pretty_name.to_string(), $func),
                )
                .expect("Macro did not set core function properly");
        };
        ($repl_env:ident += $func:ident as $name:expr) => {
            $repl_env
                .set(
                    &MalType::Symbol($name.to_string()),
                    MalType::LiftedFunc(stringify!($func).to_string(), $func),
                )
                .expect("Macro did not set core function properly");
        };
        ($repl_env:ident += $func:ident , $pretty_name:expr) => {
            $repl_env
                .set(
                    &MalType::Symbol(stringify!($func).to_string()),
                    MalType::LiftedFunc($pretty_name.to_string(), $func),
                )
                .expect("Macro did not set core function properly");
        };
        ($repl_env:ident += $func:ident) => {
            $repl_env
                .set(
                    &MalType::Symbol(stringify!($func).to_string()),
                    MalType::LiftedFunc(stringify!($func).to_string(), $func),
                )
                .expect("Macro did not set core function properly");
        };
    }

    /// Creates a new environment with basic 4 function arithmetic operations
    pub fn create_core_environment() -> Env {
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
        env
    }

    /// A function that adds some predefined function as user defined function
    pub fn add_premade_lisp_fn_to(env: &mut Env) -> &mut Env {
        // Not function
        rep(String::from("(def! not (fn* (a) (if a false true)))"), env).unwrap();
        env
    }
}

#[derive(Debug)]
/// Union of all the types of errors in the program
pub enum ReplError {
    Parse(ParseError),
    Eval(String),
}

fn new_eval_error<T>(msg: String) -> Result<T, ReplError> {
    Err(ReplError::Eval(msg))
}

fn eval_error<T>(msg: &str) -> Result<T, ReplError> {
    Err(ReplError::Eval(msg.to_string()))
}

/// Read in a string and parse it into an AST expression
fn read(line: String) -> Result<MalType, ReplError> {
    let expr = *reader::read_str(&line).map_err(ReplError::Parse)?;
    Ok(expr)
}

/// Evaluate an expression with a given environment
fn eval_ast(expr: MalType, env: Env) -> Result<MalType, ReplError> {
    match expr {
        sym @ MalType::Symbol(_) => env.get(&sym),
        ref typ @ MalType::List(ref list) | ref typ @ MalType::Vector(ref list) => {
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
                MalType::List(_) => new_list.map(MalType::List),
                MalType::Vector(_) => new_list.map(MalType::Vector),
                _ => unreachable!("MalType not a vector or list but we bound to it in the previous match, impossible!")
            }
        }
        MalType::Map(m) => {
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
            new_map.map(MalType::Map)
        }
        _ => Ok(expr),
    }
}

/// Evaluate the given expression and return the result
fn eval(ast: MalType, env: Env) -> Result<MalType, ReplError> {
    let mut current_ast = ast;
    let mut current_env = env;
    let return_value: Result<MalType, ReplError> = 'tco: loop {
        if let MalType::List(ast_expr) = current_ast.clone() {
            match ast_expr.as_slice() {
                // Special case: Empty list
                [] => break 'tco Ok(current_ast),
                [MalType::SpecialForm(SpecialKeyword::Def), key @ MalType::Symbol(_), val, ..] => {
                    let evaluated = eval(val.clone(), current_env.clone())?;
                    break 'tco current_env.set(key, evaluated);
                }
                [MalType::SpecialForm(SpecialKeyword::Def), MalType::Symbol(_)] => {
                    break 'tco eval_error("No value to bind to symbol")
                }
                [MalType::SpecialForm(SpecialKeyword::Def)] => {
                    break 'tco eval_error("No symbol to define")
                }
                [MalType::SpecialForm(SpecialKeyword::Def), ..] => {
                    break 'tco eval_error("Not a valid do-form")
                }
                [MalType::SpecialForm(SpecialKeyword::Let), MalType::List(binds) | MalType::Vector(binds), let_ast, ..] =>
                {
                    current_env = Env::new(Some(current_env.clone()));
                    for (key, val) in binds.iter().step_by(2).zip(binds.iter().skip(1).step_by(2)) {
                        match key {
                            sym @ MalType::Symbol(_) => {
                                let evaluated_val = eval(val.clone(), current_env.clone())?;
                                current_env.set(sym, evaluated_val)?;
                            }
                            _ => break 'tco eval_error(&format!("Binding to non-symbol: {}", key)),
                        }
                    }
                    current_ast = let_ast.clone();
                    continue 'tco;
                }
                [MalType::SpecialForm(SpecialKeyword::Let), MalType::List(_) | MalType::Vector(_)] => {
                    break 'tco eval_error("No item to process in let*")
                }
                [MalType::SpecialForm(SpecialKeyword::Let)] => {
                    break 'tco eval_error("No bindings found")
                }
                [MalType::SpecialForm(SpecialKeyword::Do), between @ .., last] => {
                    let _ = eval_ast(MalType::List(between.to_vec()), current_env.clone());
                    current_ast = last.clone();
                    continue 'tco;
                }
                [MalType::SpecialForm(SpecialKeyword::Do)] => {
                    break 'tco eval_error("Do form has nothing to do")
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
                    break 'tco eval_error("No cases to evaluate after condition");
                }
                [MalType::SpecialForm(SpecialKeyword::If)] => {
                    break 'tco eval_error("No condition to evaluate");
                }
                [MalType::SpecialForm(SpecialKeyword::Fn), MalType::List(param_syms) | MalType::Vector(param_syms), fn_ast, ..] =>
                {
                    let Ok(params) = param_syms.iter().try_fold(Vec::new(), |mut list, sym| {
                        if let MalType::Symbol(s) = sym {
                            list.push(s.clone());
                            Ok(list)
                        } else {
                            Err(())
                        }
                    }) else {
                        break 'tco eval_error("Parameters must all be symbols")
                    };
                    break 'tco Ok(MalType::MalFunc {
                        fn_ast: Box::new(fn_ast.clone()),
                        params,
                        fn_env: current_env.clone(),
                        fn_val: Box::new(MalType::Nil(())),
                    });
                }
                [MalType::SpecialForm(SpecialKeyword::Fn), MalType::List(_) | MalType::Vector(_)] => {
                    break 'tco eval_error("Function definition has no body")
                }
                [MalType::SpecialForm(SpecialKeyword::Fn), _, ..] => {
                    break 'tco eval_error("Function parameters must be a list or vector")
                }
                [MalType::SpecialForm(SpecialKeyword::Fn)] => {
                    break 'tco eval_error("Function definition got no parameters list")
                }
                _ => match eval_ast(current_ast, current_env) {
                    Ok(MalType::List(res_list)) => match res_list.as_slice() {
                        [MalType::LiftedFunc(_, f), args @ ..] => {
                            break 'tco f(args.into()).map_err(ReplError::Eval)
                        }
                        [MalType::MalFunc {
                            fn_ast,
                            params,
                            fn_env,
                            fn_val: _,
                        }, args @ ..] => {
                            current_ast = (**fn_ast).clone();
                            current_env = Env::with_bindings(Some(fn_env.clone()), params, args)?;
                        }
                        [_, ..] => break 'tco eval_error("Expected first item to be a function"),
                        [] => break 'tco eval_error("Function not found"),
                    },
                    Ok(_) => break 'tco eval_error("Expected a list"),
                    Err(err) => break 'tco Err(err),
                },
            };
        } else {
            // Otherwise, just evaluate the ast and return the result
            break 'tco eval_ast(current_ast, current_env.clone());
        }
    };
    return_value
}

/// Print a given AST
fn print(value: MalType) {
    println!("{}", printer::pr_str(value, true))
}

/// Runs the read, evaluate, and print functions in that order
fn rep(line: String, env: &Env) -> Result<(), ReplError> {
    let ast = read(line)?;
    let res = eval(ast, env.clone())?;
    print(res);
    Ok(())
}

/// Runs the repl
pub fn main() -> rustyline::Result<()> {
    let mut rl = DefaultEditor::new()?;
    let mut repl_env = create_core_environment();
    add_premade_lisp_fn_to(&mut repl_env);
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
    use super::{
        core::{add_premade_lisp_fn_to, create_core_environment},
        *,
    };
    static mut OUTPUT: Vec<String> = vec![];

    pub fn simulate_print(args: Vec<MalType>) -> Result<MalType, String> {
        let string = core::stringify_args(args, true, Some(" "));
        unsafe { OUTPUT.push(string) };
        Ok(MalType::Nil(()))
    }
    pub fn simulate_println(args: Vec<MalType>) -> Result<MalType, String> {
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
        let mut test_env = create_core_environment();
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

    fn run_test(file: &str, mut test_env: Env, print_line: bool) {
        let _ = test_env.set(
            &MalType::Symbol("prn".to_string()),
            MalType::LiftedFunc("Simulate Print".to_string(), simulate_print),
        );
        let _ = test_env.set(
            &MalType::Symbol("println".to_string()),
            MalType::LiftedFunc("Simulate Println".to_string(), simulate_println),
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
                        printer::pr_str(success.clone(), true),
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
