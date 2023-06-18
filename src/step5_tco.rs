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
        List(VecDeque<MalType>),
        Vector(VecDeque<MalType>),
        Map(Vec<(MalType, MalType)>),
        LiftedFunc(String, fn(VecDeque<MalType>, &mut Env) -> MalResult),
        UserFunc(Vec<String>, Box<MalType>, Env),
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
                (Self::UserFunc(l0, l1, l2), Self::UserFunc(r0, r1, r2)) => {
                    l0 == r0 && l1 == r1 && l2 == r2
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
        let mut list = VecDeque::new();
        let mut rem = lex_list;
        while let Some(token) = rem.get(0) {
            match token {
                Token::CloseBracket => {
                    rem.pop_front();
                    return Ok((MalType::Vector(list), rem));
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
            MalType::Keyword(k) => k.to_string(),
            MalType::SpecialForm(k) => k.to_string(),
            MalType::Symbol(s) => s.to_string(),
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
            MalType::UserFunc(p, b, _) => {
                format!("(fn* ({}) {}", p.join(" "), pr_str(*b, print_readably))
            }
        }
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

        /// Create a new environment with outer (parent) environment and bindings (parameters to expressions).
        ///
        /// If provided with another environment, it will add all items different from outer to data.
        pub fn with_outer_and_bindings(
            outer: Box<Env>,
            binds: Vec<String>,
            exprs: Vec<MalType>,
            other: Option<&Env>,
        ) -> Self {
            let mut data = HashMap::new();
            if let Some(other) = other {
                data.extend(
                    other
                        .data
                        .iter()
                        // Skip over anything found in outer environment
                        .filter(|(k, _)| !outer.data.contains_key(&(*k).clone()))
                        .map(|(k, v)| (k.clone(), v.clone())),
                )
            }
            let mut variadic_start = None;
            for (i, b) in binds.clone().into_iter().enumerate() {
                if b == "&" {
                    variadic_start = Some(i + 1);
                    break;
                } else {
                    data.insert(b, exprs.get(i).cloned().unwrap_or(MalType::Nil(())));
                }
            }
            if let Some(start) = variadic_start {
                if let Some(b) = binds.get(start) {
                    data.insert(
                        b.to_string(),
                        // HACK: to_vec -> into (cannot go straight to vecdeque for slices)
                        MalType::List(exprs[(start - 1)..].to_vec().into()),
                    );
                }
            }
            Self {
                outer: Some(outer),
                data,
            }
        }

        /// Takes a symbol key and a mal value, adds it to the environment
        pub fn set(&mut self, key: String, val: MalType) -> &mut Self {
            self.data.insert(key, val);
            self
        }

        /// Same as set(), but take a mal value symbol
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

        /// Same as find(), but take a mal value symbol
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

        /// Same as get(), but take a mal value symbol
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

    use super::{env::Env, printer::pr_str, reader::MalType, rep, MalResult};

    /// Apply pr_str to each argument and join them together
    pub fn stringify_args(
        args: VecDeque<MalType>,
        print_readably: bool,
        join_str: Option<&str>,
    ) -> String {
        args.into_iter()
            .map(|a| pr_str(a, print_readably))
            .collect::<Vec<_>>()
            .join(join_str.unwrap_or(""))
    }
    /// Makes each argument to their readable (escaped) string representation and concatenates them into a single string type.
    pub fn pr_dash_str(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        Ok(MalType::String(stringify_args(args, true, Some(" "))))
    }

    /// Makes each argument to their string representation and concatenates them into a single string type.
    pub fn str(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        Ok(MalType::String(stringify_args(args, false, None)))
    }

    /// Makes each argument to their readable (escaped) string representation, concatenates them, and then prints the result to console.
    pub fn prn(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        println!("{}", stringify_args(args, true, Some(" ")));
        Ok(MalType::Nil(()))
    }

    /// Makes each argument to their string representation, concatenates them, and then prints the result to console.
    pub fn println(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        println!("{}", stringify_args(args, false, Some(" ")));
        Ok(MalType::Nil(()))
    }

    /// Convert all arguments to a list
    pub fn to_list(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        Ok(MalType::List(args))
    }

    /// Check if first argument is a list
    pub fn is_list(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        match args.get(0) {
            Some(MalType::List(_)) => Ok(MalType::Bool(true)),
            Some(_) => Ok(MalType::Bool(false)),
            None => Err("Not enough arguments".to_string()),
        }
    }

    /// Check if first argument is empty
    pub fn is_empty(args: VecDeque<MalType>, _env: &mut Env) -> MalResult {
        match args.get(0) {
            Some(MalType::List(l)) => Ok(MalType::Bool(l.is_empty())),
            Some(MalType::Vector(v)) => Ok(MalType::Bool(v.is_empty())),
            Some(MalType::Map(m)) => Ok(MalType::Bool(m.is_empty())),
            Some(_) => Err("Is emptyonly works only with non-atomics types".to_string()),
            None => Err("Not enough arguments".to_string()),
        }
    }

    /// Check the number of elements in first argument
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
        rep(String::from("(def! not (fn* (a) (if a false true)))"), env).unwrap();
        env
    }
}

#[derive(Debug)]
/// Union of all the types of errors in the program
enum ReplError {
    Parse(ParseError),
    Eval(String),
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
fn eval_ast(expr: MalType, env: &mut Env) -> Result<MalType, ReplError> {
    match expr {
        MalType::Symbol(s) => env.get(s).map_err(ReplError::Eval),
        ref typ @ MalType::List(ref vd) | ref typ @ MalType::Vector(ref vd) => {
            let new_list =
                vd.iter()
                    .map(|e| eval(e.clone(), env))
                    .try_fold(VecDeque::new(), |mut list, r| {
                        if let Ok(e) = r {
                            list.push_back(e);
                            Ok(list)
                        } else {
                            Err(r.unwrap_err())
                        }
                    });
            match typ {
                MalType::List(_) => new_list.map(MalType::List),
                MalType::Vector(_) => new_list.map(MalType::Vector),
                _ => unreachable!("MalType not a vector or list but we bound to it in the previous match, impossible!")
            }
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
    let mut current_ast = ast;
    let mut current_env = env;
    'tco: loop {
        match current_ast.clone() {
            MalType::List(ref v) if v.is_empty() => return Ok(current_ast),
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
                        let evaluated_val = eval(val, current_env)?;
                        current_env.set(key, evaluated_val.clone());
                        return Ok(evaluated_val);
                    }
                    // FIXME: Environment leaks outside of let
                    MalType::SpecialForm(SpecialKeyword::Let) => {
                        let mut new_env = Env::with_outer(Box::new(current_env.clone()));
                        match ast_expr.pop_front() {
                            Some(MalType::List(binds)) | Some(MalType::Vector(binds)) => {
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
                                let Some(body) = ast_expr.pop_front() else {
                                return eval_error("Second argument empty");
                            };
                                *current_env = new_env;
                                current_ast = body;
                                continue 'tco;
                            }
                            Some(_) => {
                                return eval_error("Non-list binding found for let*");
                            }
                            None => {
                                return eval_error("No values to bind in environment");
                            }
                        }
                    }
                    MalType::SpecialForm(SpecialKeyword::Do) => {
                        let _ = eval_ast(
                            MalType::List(
                                ast_expr
                                    .range(..ast_expr.len() - 1)
                                    .cloned()
                                    .collect::<VecDeque<_>>(),
                            ),
                            current_env,
                        );
                        current_ast = ast_expr.back().cloned().unwrap_or(MalType::Nil(()));
                        continue 'tco;
                    }
                    MalType::SpecialForm(SpecialKeyword::If) => {
                        let Some(cond) = ast_expr.pop_front() else {
                        return eval_error("No condition for if form given");
                    };
                        match eval(cond, current_env) {
                            Ok(MalType::Nil(()) | MalType::Bool(false)) => {
                                ast_expr.pop_front();
                                current_ast = ast_expr.pop_front().unwrap_or(MalType::Nil(()));
                            }
                            Ok(_) => {
                                if let Some(true_branch) = ast_expr.pop_front() {
                                    current_ast = true_branch;
                                    continue 'tco;
                                } else {
                                    return eval_error("No true branch to evaluate");
                                }
                            }
                            Err(_) => {
                                return eval_error("Failed to evaluate condition");
                            }
                        }
                    }
                    MalType::SpecialForm(SpecialKeyword::Fn) => {
                        let params = match ast_expr.pop_front() {
                            Some(MalType::List(l)) => {
                                l.into_iter().try_fold(Vec::new(), |mut acc, m| match m {
                                    MalType::Symbol(s) => {
                                        acc.push(s);
                                        Ok(acc)
                                    }
                                    _ => eval_error(&format!("Not a symbol: {:?}", m)),
                                })?
                            }
                            Some(MalType::Vector(v)) => {
                                v.into_iter().try_fold(Vec::new(), |mut acc, m| match m {
                                    MalType::Symbol(s) => {
                                        acc.push(s);
                                        Ok(acc)
                                    }
                                    _ => eval_error(&format!("Not a symbol: {:?}", m)),
                                })?
                            }
                            _ => return eval_error("No parameter list found"),
                        };
                        let Some(body) = ast_expr.pop_front() else {
                        return eval_error("Function body not defined");
                    };
                        // Ok(MalType::UserFunc(params, Box::new(body), env.clone()))
                        unimplemented!()
                    }
                    _ => match eval_ast(current_ast, current_env)? {
                        MalType::List(mut list) => {
                            let Some(func) = list.pop_front() else {
                            return eval_error("Function not defined");
                        };
                            match func {
                                MalType::LiftedFunc(_, func) => {
                                    return func(list, current_env).map_err(ReplError::Eval)
                                }
                                MalType::UserFunc(params, body, outer_env) => {
                                    let mut fn_env = Env::with_outer_and_bindings(
                                        Box::new(outer_env),
                                        params,
                                        list.into(),
                                        Some(&current_env),
                                    );
                                    // eval(*body, &mut fn_env)
                                    unimplemented!()
                                }
                                non_func => {
                                    return eval_error(&format!(
                                        "Expected a function, got {non_func}"
                                    ));
                                }
                            }
                        }
                        non_list => {
                            return eval_error(&format!("Expected a list, got {non_list}"));
                        }
                    },
                }
            }
            _ => return eval_ast(current_ast, current_env),
        }
    }
}

/// Print a given AST
fn print(value: MalType) {
    println!("{}", printer::pr_str(value, true))
}

/// Runs the read, evaluate, and print functions in that order
fn rep(line: String, env: &mut Env) -> Result<(), ReplError> {
    let ast = read(line)?;
    let res = eval(ast, env)?;
    print(res);
    Ok(())
}

/// Runs the repl
pub fn main() -> rustyline::Result<()> {
    let mut rl = DefaultEditor::new()?;
    let mut repl_env = create_core_environment();
    // add_premade_lisp_fn_to(&mut repl_env);
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
        if let Err(err) = rep(line, &mut repl_env) {
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
    use super::{core::create_core_environment, *};
    static mut OUTPUT: Vec<String> = vec![];

    pub fn simulate_print(args: VecDeque<MalType>, _env: &mut Env) -> Result<MalType, String> {
        let string = core::stringify_args(args, true, Some(" "));
        unsafe { OUTPUT.push(string) };
        Ok(MalType::Nil(()))
    }
    pub fn simulate_println(args: VecDeque<MalType>, _env: &mut Env) -> Result<MalType, String> {
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
        run_test(file, make_test_env());
    }
    #[test]
    fn step_4_eval_tester() {
        let file = include_str!("../tests/step4_if_fn_do.mal");
        run_test(file, make_test_env());
    }

    #[test]
    fn step_5_eval_tester() {
        let file = include_str!("../tests/step5_tco.mal");
        run_test(file, make_test_env());
    }

    fn run_test(file: &str, mut test_env: Env) {
        test_env.set(
            "prn".to_string(),
            MalType::LiftedFunc("Simulate Print".to_string(), simulate_print),
        );
        test_env.set(
            "println".to_string(),
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
                    &mut test_env,
                );
            }
        }
    }
}
