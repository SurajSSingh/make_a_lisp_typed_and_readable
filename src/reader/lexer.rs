//! Module containing the lexer

use std::{cell::RefCell, collections::VecDeque, fmt::Display, rc::Rc, vec};

use fraction::DynaDecimal;
use logos::Logos;

use crate::{old_env::Env, old_repl::MalResult, types::error::LexError};

#[derive(Logos, Clone, Debug, PartialEq)]
#[logos(error=LexError, skip r"[ \t\n\f]+")]
/// Token produced from the lexing step
pub enum Token<'t> {
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
    #[regex(r";.*")]
    /// Comment: Semicolon ... Stuff in between ... until \n
    Comment(&'t str),

    // Symbols

    //Literals
    /// Character
    Character(char),

    // #[regex(r#""(?:\\.|[^\\"])*"?"#)]
    #[regex(r#""(([^"]*(\\.)*))*""#)]
    /// String: Open Quote ... Stuff in between ... Close Quote
    StringTok(&'t str),

    /// Integer: digit+
    Number(DynaDecimal<u64, u16>),

    #[regex(r#"[^\s\[\]{}('"`,;~@)]*"#)]
    /// Atom: Anything else, should be catch all
    ///
    /// Note: Atom disallows ~ and @ because of Logos's parsing rule; this is not in original regex
    Atom(&'t str),
}

pub fn tokenize(input: &str) -> logos::Lexer<'_, Token<'_>> {
    Token::lexer(input)
}
