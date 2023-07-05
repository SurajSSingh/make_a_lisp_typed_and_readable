use std::{cell::RefCell, collections::VecDeque, fmt::Display, rc::Rc, vec};

use logos::Logos;

use crate::{old_env::Env, old_repl::MalResult};

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
    Quote,
    Quasiquote,
    Unquote,
    SpliceUnquote,
    DefMacro,
    MacroExpand,
    Try,
    Catch,
}

impl Display for SpecialKeyword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpecialKeyword::Def => f.write_str("def!"),
            SpecialKeyword::Let => f.write_str("let*"),
            SpecialKeyword::Do => f.write_str("do"),
            SpecialKeyword::If => f.write_str("if"),
            SpecialKeyword::Fn => f.write_str("fn*"),
            SpecialKeyword::Quote => f.write_str("quote"),
            SpecialKeyword::Quasiquote => f.write_str("quasiquote"),
            SpecialKeyword::Unquote => f.write_str("unquote"),
            SpecialKeyword::SpliceUnquote => f.write_str("splice-unquote"),
            SpecialKeyword::DefMacro => f.write_str("defmacro!"),
            SpecialKeyword::MacroExpand => f.write_str("macroexpand"),
            SpecialKeyword::Try => f.write_str("try*"),
            SpecialKeyword::Catch => f.write_str("catch*"),
        }
    }
}

#[derive(Clone)]
/// Basic Types with in the interpreter
pub enum MalType {
    Nil(()),
    Bool(bool),
    Number(f64),
    Keyword(String),
    /// Holds any special symbols
    SpecialForm(SpecialKeyword),
    Symbol(String),
    String(String),
    List(Vec<MalType>, Box<MalType>),
    Vector(Vec<MalType>, Box<MalType>),
    Map(Vec<(MalType, MalType)>, Box<MalType>),
    LiftedFunc(String, fn(Vec<MalType>) -> MalResult, Box<MalType>),
    MalFunc {
        fn_ast: Box<MalType>,
        params: Vec<String>,
        fn_env: Env,
        fn_val: Box<MalType>,
        is_macro: bool,
        meta: Box<MalType>,
    },
    Atom(Rc<RefCell<MalType>>),
}

impl MalType {
    pub fn get_type(&self) -> String {
        match self {
            MalType::Nil(_) => "Nil".to_string(),
            MalType::Bool(_) => "Bool".to_string(),
            MalType::Number(_) => "Number".to_string(),
            MalType::Keyword(_) => "Keyword".to_string(),
            MalType::SpecialForm(form) => format!("Special-Form: {form}"),
            MalType::Symbol(_) => "Symbol".to_string(),
            MalType::String(_) => "String".to_string(),
            MalType::List(_, _) => "List".to_string(),
            MalType::Vector(_, _) => "Vector".to_string(),
            MalType::Map(_, _) => "Map".to_string(),
            MalType::LiftedFunc(_, _, _) => "Built-in Function".to_string(),
            MalType::MalFunc { .. } => "User Function".to_string(),
            MalType::Atom(_) => "Atom".to_string(),
        }
    }
}

impl PartialEq for MalType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            // Default cases
            (Self::Nil(l0), Self::Nil(r0)) => l0 == r0,
            (Self::Bool(l0), Self::Bool(r0)) => l0 == r0,
            (Self::Number(l0), Self::Number(r0)) => l0 == r0,
            (Self::Keyword(l0), Self::Keyword(r0)) => l0 == r0,
            (Self::SpecialForm(l0), Self::SpecialForm(r0)) => l0 == r0,
            (Self::Symbol(l0), Self::Symbol(r0)) => l0 == r0,
            (Self::String(l0), Self::String(r0)) => l0 == r0,
            (Self::List(l0, _), Self::List(r0, _)) => l0 == r0,
            (Self::Vector(l0, _), Self::Vector(r0, _)) => l0 == r0,
            (Self::Map(l0, _), Self::Map(r0, _)) => l0
                .iter()
                .all(|(k1, v1)| r0.iter().any(|(k2, v2)| k1 == k2 && v1 == v2)),
            (Self::Atom(a0), Self::Atom(a1)) => a0 == a1,
            (Self::LiftedFunc(l0, _l1, _), Self::LiftedFunc(r0, _r1, _)) => l0 == r0,
            (
                Self::MalFunc {
                    fn_ast: _ast0,
                    params: _p0,
                    fn_env: _env0,
                    fn_val: _fn0,
                    is_macro: _m0,
                    meta: _meta0,
                },
                Self::MalFunc {
                    fn_ast: _ast1,
                    params: _p1,
                    fn_env: _env1,
                    fn_val: _fn1,
                    is_macro: _m1,
                    meta: _meta1,
                },
            ) => {
                // FIXME: Currently, no two mal functions are the same
                false
            }
            // Special case: Equal length List and Vector
            (Self::List(lst, _), Self::Vector(vec, _))
            | (Self::Vector(vec, _), Self::List(lst, _))
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
            Self::Number(arg0) => f.debug_tuple("Number").field(arg0).finish(),
            Self::Keyword(arg0) => f.debug_tuple("Keyword").field(arg0).finish(),
            Self::SpecialForm(arg0) => f.debug_tuple("SpecialForm").field(arg0).finish(),
            Self::Symbol(arg0) => f.debug_tuple("Symbol").field(arg0).finish(),
            Self::String(arg0) => f.debug_tuple("String").field(arg0).finish(),
            Self::List(arg0, _) => f.debug_tuple("List").field(arg0).finish(),
            Self::Vector(arg0, _) => f.debug_tuple("Vector").field(arg0).finish(),
            Self::Map(arg0, _) => f.debug_tuple("Map").field(arg0).finish(),
            Self::LiftedFunc(arg0, _arg1, _) => f.debug_tuple("LiftedFunc").field(arg0).finish(),
            Self::MalFunc {
                fn_ast,
                params,
                fn_env,
                fn_val,
                is_macro,
                meta: _meta,
            } => f
                .debug_struct("MalFunc")
                .field("fn_ast", fn_ast)
                .field("params", params)
                .field("fn_env", fn_env)
                .field("fn_val", fn_val)
                .field("is_macro", is_macro)
                .finish(),
            Self::Atom(a) => f.debug_tuple("Atom").field(a).finish(),
        }
    }
}

impl Display for MalType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&super::old_printer::pr_str(self.clone(), true))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct SpannedMalType {
    value: MalType,
    span: logos::Span,
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
fn tokenize(input: &str) -> VecDeque<Token> {
    Box::new(Token::lexer(input).filter_map(|res| res.ok()))
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
                Ok((
                    MalType::List(
                        vec![MalType::SpecialForm(SpecialKeyword::Quote), form],
                        Box::new(MalType::Nil(())),
                    ),
                    remaining,
                ))
            }
            Token::Quasiquote => {
                lex_list.pop_front();
                let (form, remaining) = read_form(lex_list)?;
                Ok((
                    MalType::List(
                        vec![MalType::SpecialForm(SpecialKeyword::Quasiquote), form],
                        Box::new(MalType::Nil(())),
                    ),
                    remaining,
                ))
            }
            Token::Deref => {
                lex_list.pop_front();
                let (form, remaining) = read_form(lex_list)?;
                Ok((
                    MalType::List(
                        vec![MalType::Symbol("deref".to_string()), form],
                        Box::new(MalType::Nil(())),
                    ),
                    remaining,
                ))
            }
            Token::Meta => {
                lex_list.pop_front();
                let (meta, rem1) = read_form(lex_list)?;
                let (form, rem2) = read_form(rem1)?;
                Ok((
                    MalType::List(
                        vec![MalType::Symbol("with-meta".to_string()), form, meta],
                        Box::new(MalType::Nil(())),
                    ),
                    rem2,
                ))
            }
            Token::Unquote => {
                lex_list.pop_front();
                if let Some(token2) = lex_list.get(0) {
                    if matches!(token2, Token::Deref) {
                        lex_list.pop_front();
                        let (form, remaining) = read_form(lex_list)?;
                        Ok((
                            MalType::List(
                                vec![MalType::SpecialForm(SpecialKeyword::SpliceUnquote), form],
                                Box::new(MalType::Nil(())),
                            ),
                            remaining,
                        ))
                    } else {
                        let (form, remaining) = read_form(lex_list)?;
                        Ok((
                            MalType::List(
                                vec![MalType::SpecialForm(SpecialKeyword::Unquote), form],
                                Box::new(MalType::Nil(())),
                            ),
                            remaining,
                        ))
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
                return Ok((MalType::List(list, Box::new(MalType::Nil(()))), rem));
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
                return Ok((MalType::Vector(list, Box::new(MalType::Nil(()))), rem));
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
/// * {"a" 1} -> **OK**: MalType::Map({"a":1})
/// * {"a" 1} -> **ERR**: Unbalanced Parenthesis
fn read_hashmap<'t>(
    lex_list: &'t mut VecDeque<Token<'t>>,
) -> Result<(MalType, &'t mut VecDeque<Token<'t>>), ParseError> {
    let mut map = Vec::new();
    let mut rem = lex_list;
    while let Some(token) = rem.get(0) {
        match token {
            Token::CloseBrace => {
                rem.pop_front();
                return Ok((MalType::Map(map, Box::new(MalType::Nil(()))), rem));
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
                        "defmacro!" => {
                            Ok((MalType::SpecialForm(SpecialKeyword::DefMacro), lex_list))
                        }
                        "macroexpand" => {
                            Ok((MalType::SpecialForm(SpecialKeyword::MacroExpand), lex_list))
                        }
                        "quote" => Ok((MalType::SpecialForm(SpecialKeyword::Quote), lex_list)),
                        "quasiquote" => {
                            Ok((MalType::SpecialForm(SpecialKeyword::Quasiquote), lex_list))
                        }
                        "unquote" => Ok((MalType::SpecialForm(SpecialKeyword::Unquote), lex_list)),
                        "splice-unquote" => Ok((
                            MalType::SpecialForm(SpecialKeyword::SpliceUnquote),
                            lex_list,
                        )),
                        "try*" => Ok((MalType::SpecialForm(SpecialKeyword::Try), lex_list)),
                        "catch*" => Ok((MalType::SpecialForm(SpecialKeyword::Catch), lex_list)),
                        c if c.starts_with(':') => {
                            Ok((MalType::Keyword(atom.to_string()), lex_list))
                        }
                        _ => Ok((MalType::Symbol(atom.to_string()), lex_list)),
                    }
                }
            }
            c => {
                dbg!(c);
                unreachable!()
            }
        }
    } else {
        Err(ParseError::Eof)
    }
}
