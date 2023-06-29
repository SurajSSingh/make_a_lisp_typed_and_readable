//! This file contains all items related to the lexical phase of the program.
//! It takes a string representing the line being lexed and converts it into a linear structure of Tokens.

use std::num::ParseIntError;

use imstr::ImString;
use logos::{Lexer, Logos, Span};
use num_rational::Ratio;
use ordered_float::OrderedFloat;

type LexResult<T> = Result<T, LexError>;

// pub trait FromLexer {
//     fn from_lexer(lex: &mut logos::Lexer<NewToken>) -> Option<Self>;
// }

/// Whitespace level
#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Default,
    derive_more::From,
    derive_more::Into,
)]
pub struct WhitespaceLevel {
    space: usize,
    tab: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PunctuationType {
    /// Represents ()
    Parenthesis,
    /// Represents []
    Bracket,
    /// Represents {}
    Brace,
    Other(char),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecialReaderSymbol {
    /// Single quote
    Quote,
    /// Caret
    Metadata,
    /// At-sign
    Deref,
    /// Backtick
    SyntaxQuote,
    /// Tilde
    Unquote,
    /// Tilde + At
    UnquoteSplice,
    /// Octothorpe
    Dispatch,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub enum LexError {
    #[default]
    Default,
    NumberParse,
    InvalidCharacter(String),
}

fn lex_whitespace(lex: &mut Lexer<NewToken>) -> WhitespaceLevel {
    lex.slice()
        .chars()
        .fold((0, 0), |acc, s| match s {
            ' ' => (acc.0 + 1, acc.1),
            '\t' => (acc.0, acc.1 + 1),
            _ => unreachable!("Got a non-whitespace character"),
        })
        .into()
}

fn lex_punctuation(lex: &mut Lexer<NewToken>) -> PunctuationType {
    match lex.slice() {
        "(" | ")" => PunctuationType::Parenthesis,
        "[" | "]" => PunctuationType::Bracket,
        "{" | "}" => PunctuationType::Brace,
        other => PunctuationType::Other(other.chars().next().expect("At least one character")),
    }
}

fn lex_symbol(lex: &mut Lexer<NewToken>) -> LexResult<SpecialReaderSymbol> {
    match lex.slice() {
        "'" => Ok(SpecialReaderSymbol::Quote),
        "`" => Ok(SpecialReaderSymbol::SyntaxQuote),
        "~" => Ok(SpecialReaderSymbol::Unquote),
        "~@" => Ok(SpecialReaderSymbol::UnquoteSplice),
        "@" => Ok(SpecialReaderSymbol::Deref),
        "^" => Ok(SpecialReaderSymbol::Metadata),
        "#" => Ok(SpecialReaderSymbol::Dispatch),
        c => Err(LexError::InvalidCharacter(c.to_string())),
    }
}

fn lex_integer(lex: &mut Lexer<NewToken>) -> LexResult<i64> {
    lex.slice()
        .parse::<i64>()
        .map_err(|_| LexError::NumberParse)
}

fn lex_rational(lex: &mut Lexer<NewToken>) -> LexResult<(bool, Ratio<u32>)> {
    let mut slice = lex.slice();
    let sign = if slice.starts_with('-') {
        slice = slice.strip_prefix('-').unwrap_or(slice);
        false
    } else if slice.starts_with('+') {
        slice = slice.strip_prefix('+').unwrap_or(slice);
        true
    } else {
        true
    };
    let num = slice.parse::<u32>().map_err(|_| LexError::NumberParse)?;
    let dem = slice.parse::<u32>().map_err(|_| LexError::NumberParse)?;
    Ok((sign, Ratio::from((num, dem))))
}

fn lex_float(lex: &mut Lexer<NewToken>) -> LexResult<OrderedFloat<f64>> {
    lex.slice()
        .parse::<f64>()
        .map(|f| OrderedFloat(f))
        .map_err(|_| LexError::NumberParse)
}

pub fn lex_string(lex: &mut Lexer<NewToken>) -> LexResult<ImString> {
    Ok(ImString::from(lex.slice()))
}

pub fn lex_character(lex: &mut Lexer<NewToken>) -> LexResult<char> {
    let slice = lex.slice();
    if slice.is_empty() {
        return Err(LexError::InvalidCharacter(slice.to_string()));
    }
    let (_backslash, character) = slice.split_at(1);

    // Single UTF-8 character
    if character.len() == 1 {
        match character.chars().next() {
            Some(c) => Ok(c),
            None => Err(LexError::InvalidCharacter(character.to_string())),
        }
    }
    // 4-numbered Unicode literal
    else if character.len() == 5 {
        let (_u, code) = character.split_at(1);
        let number = u32::from_str_radix(code, 16).map_err(|_| LexError::NumberParse)?;
        match char::from_u32(number) {
            Some(c) => Ok(c),
            None => Err(LexError::InvalidCharacter(character.to_string())),
        }
    }
    // Special characters
    else {
        match character {
            "newline" => Ok('\n'),
            "space" => Ok(' '),
            "tab" => Ok('\t'),
            "formfeed" => Ok('\u{000C}'),
            "backspace" => Ok('\u{0008}'),
            "return" => Ok('\r'),
            _ => Err(LexError::InvalidCharacter(character.to_string())),
        }
    }
}

#[derive(Logos, Clone, Debug, PartialEq, Eq)]
#[logos(error = LexError)]
pub enum NewToken {
    #[regex(r";.*")]
    /// Comment: Semicolon ... Stuff in between ... until before \n
    Comment,

    #[regex(r"[ \t]+", lex_whitespace, priority = 10)]
    /// Any non-line break whitespace
    Whitespace(WhitespaceLevel),

    #[regex(r"[\n\f\r]+", |b| b.slice().len(), priority = 10)]
    /// Any line breaking whitespace
    LineBreak(usize),

    #[regex(r"[\(\[\{]", lex_punctuation)]
    /// Opening Punctuation mark, subset of \p{Open_Punctuation}
    OpenPunctuation(PunctuationType),

    #[regex(r"[\)\]\}]", lex_punctuation)]
    /// Close Punctuation marks, subset of \p{Close_Punctuation}
    ClosePunctuation(PunctuationType),

    #[regex(r"('|\^|@|`|~(@)?|#)", lex_symbol, priority = 10)]
    ReaderSymbol(SpecialReaderSymbol),

    // Eventually into Atomic types
    #[regex(r"(\+|-)?(0|[1-9][0-9]*)", lex_integer, priority = 10)]
    Integer(i64),

    /// Rational number
    #[regex(r"(\+|-)?(0|[1-9][0-9]*[/][1-9][0-9]*)", lex_rational)]
    Rational((bool, Ratio<u32>)),

    /// Floating point number
    #[regex(r"(\+|-)?(0|[1-9][0-9]*)[.]?[0-9]*", lex_float)]
    Float(OrderedFloat<f64>),

    /// Single UTF-8 Character or escaped 4-numbered Unicode literal or special named character
    #[regex(
        r"\\(.|u\d{4}|newline|space|tab|formfeed|backspace|return)",
        lex_character
    )]
    Character(char),

    // Old: r#""(?:\\.|[^\\"])*"?"#
    #[regex(r#""([^"\\]*(\\.[^"\\]*)*)""#, lex_string)]
    /// String Token: subset of \p{Initial_Punctuation}...\p{Final_Punctuation}?
    StringTok(ImString),

    // Tokens
    /// Nil token
    #[token("nil")]
    Nil,

    /// True Token
    #[token("true")]
    True,
    /// False Token
    #[token("false")]
    False,

    // Catch-all
    #[regex(r#"[^\s\[\]{}('"`,;)]*"#)]
    /// Atom: Anything else, should be catch all
    Atom,
}

// /// Take a string and produce a list of spanned token
// fn span_tokenize(input: &str) -> Vec<(NewToken, Span)> {
//     NewToken::lexer(input)
//         .spanned()
//         .filter_map(|(res, span)| res.ok().map(|r| (r, span)))
//         .collect()
// }

// fn dothing(input: &str) {
//     let x = span_tokenize(input);
//     let y = x.into_iter().map(|(a, b)| a).collect();
//     super::parser::Form::read_form(y);
// }
