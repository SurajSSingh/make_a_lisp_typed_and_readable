//! Module containing the lexer

use std::{cell::RefCell, collections::VecDeque, fmt::Display, rc::Rc, vec};

use fraction::DynaDecimal;
use logos::{Lexer, Logos};

use crate::{
    old_env::Env,
    old_repl::MalResult,
    types::error::{LexError, LexResult},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PunctuationCategory {
    Parenthesis,
    SquareBracket,
    CurlyBraces,
    Other(char),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReaderCharacter {
    /// # - hashtag character
    Dispatch,
    /// ' - single quote character
    Quote,
    /// @ - at-symbol character
    Deref,
    /// ^ - caret character
    Metadata,
    /// ` - backtick character
    SyntaxQuote,
    /// ~ - tilde character
    Unquote,
    /// ~@ - tilde + at-symbol
    UnquoteSplice,
}

fn lex_punctuation<'t>(lex: &mut Lexer<'t, Token<'t>>) -> PunctuationCategory {
    match lex.slice() {
        "(" | ")" => PunctuationCategory::Parenthesis,
        "[" | "]" => PunctuationCategory::SquareBracket,
        "{" | "}" => PunctuationCategory::CurlyBraces,
        c => PunctuationCategory::Other(c.chars().next().unwrap()),
    }
}

fn lex_number<'t>(lex: &mut Lexer<'t, Token<'t>>) -> LexResult<DynaDecimal<u64, u16>> {
    todo!()
}

#[derive(Logos, Clone, Debug, PartialEq)]
#[logos(error=LexError, skip r"[ \t\n\f]+")]
/// Token produced from the lexing step
pub enum Token<'t> {
    #[regex(r"\p{Ps}", lex_punctuation)]
    /// Open punctuation - parentheses/brackets/braces like
    Open(PunctuationCategory),
    /// Close punctuation - parentheses/brackets/braces like
    #[regex(r"\p{Pe}", lex_punctuation)]
    Close(PunctuationCategory),

    ///
    Special(ReaderCharacter),

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
    #[regex(r#""(([^"]*(\\.)*))*(")?"#)]
    /// String: Open Quote ... Stuff in between ... Close Quote
    StringTok(&'t str),

    /// Integer: optional('+'/'-') many1(digit)
    /// Rational: [Integer] '/' [Integer]
    /// Float: [Integer] '.' [Integer]
    /// Symbolic: ##Inf, ##-Inf, ##NaN
    #[regex(
        r"(?P<integer>\d+)|(?P<rational>\d+/\d+)|(?P<float>\d+\.\d+)|(?P<symbolic>##((-)?Inf|Nan))",
        lex_number
    )]
    Number(DynaDecimal<u64, u16>),

    Keyword(&'t str),

    #[regex(r#"[^\s\[\]{}('"`,;~@)]*"#)]
    /// Atom: Anything else, should be catch all
    ///
    /// Note: Atom disallows ~ and @ because of Logos's parsing rule; this is not in original regex
    Atom(&'t str),
}

pub fn tokenize(input: &str) -> logos::Lexer<'_, Token<'_>> {
    Token::lexer(input)
}
