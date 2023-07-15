//! Module for parsing into forms
use im::Vector;
use string_interner::symbol::SymbolUsize;

use crate::types::{
    error::{Error, LexResult, ParseError},
    value::{MaltarTrait, MaltarValue},
    MaltarResult,
};

use super::lexer::{tokenize, PunctuationCategory, ReaderCharacter, Token};

pub struct FnPart<Val>
where
    Val: Into<MaltarValue<Val>> + MaltarTrait,
{
    params: Vec<String>,
    exprs: Vec<Val>,
}
/// Form representation an evaulatable representation of the types
pub enum Form<Val>
where
    Val: Into<MaltarValue<Val>> + MaltarTrait,
{
    Def {
        symbol: SymbolUsize,
        doc_string: Option<String>,
        init: Option<Val>,
    },
    Do(Vector<Val>),
    Quote(Box<Form<Val>>),
    Var(String),
    Fn {
        name: Option<String>,
        overloads: Vec<FnPart<Val>>,
    },
    Default(Val),
}

type LexItem<'t> = LexResult<Token<'t>>;

impl<Val> Form<Val>
where
    Val: Into<MaltarValue<Val>> + MaltarTrait,
{
    pub fn read_string(input: &str) -> MaltarResult<Form<Val>> {
        let tokens = tokenize(input);
        let (form, _remaining) = Form::read_form(tokens)?;
        Ok(form)
    }

    /// Try to read next token from lexer.
    /// If lexer error, bubble up the lexer error.
    /// If no more tokens, return unexpected EOF error.
    /// Otherwise, return the token.
    pub fn try_get_next_token<'t, I>(lex: &mut I) -> MaltarResult<Token<'t>>
    where
        I: Iterator<Item = LexItem<'t>>,
    {
        lex.next()
            .transpose()?
            .ok_or(Error::Parse(ParseError::UnexpectedEOF))
    }

    /// Read a form
    pub fn read_form<'t, I>(mut lex: I) -> MaltarResult<(Form<Val>, I)>
    where
        I: Iterator<Item = LexItem<'t>>,
    {
        match Form::<Val>::try_get_next_token(&mut lex)? {
            Token::Open(pc) => Form::<Val>::read_collection(lex, pc, false),
            Token::Special(ReaderCharacter::Dispatch) => {
                match Form::<Val>::try_get_next_token(&mut lex)? {
                    Token::Open(pc) => Form::<Val>::read_collection(lex, pc, true),
                    _ => todo!(),
                }
            }
            t => Form::<Val>::read_atom(t).map(|f| (f, lex)),
        }
    }

    /// Read a collection
    pub fn read_collection<'t, I>(
        mut lex: I,
        punct: PunctuationCategory,
        dispatched: bool,
    ) -> MaltarResult<(Form<Val>, I)>
    where
        I: Iterator<Item = LexItem<'t>>,
    {
        match (dispatched, punct) {
            (true, PunctuationCategory::Parenthesis) => Form::<Val>::read_anon_func(lex),
            (true, PunctuationCategory::SquareBracket) => {
                todo!("Possibly used for infix special form")
            }
            (true, PunctuationCategory::CurlyBraces) => Form::<Val>::read_set(lex),
            (false, PunctuationCategory::Parenthesis) => Form::<Val>::read_list(lex),
            (false, PunctuationCategory::SquareBracket) => Form::<Val>::read_vector(lex),
            (false, PunctuationCategory::CurlyBraces) => Form::<Val>::read_map(lex),
            _ => todo!("Other punctuations not supported yet"),
        }
    }

    /// Read a list
    pub fn read_list<'t, I>(mut lex: I) -> MaltarResult<(Form<Val>, I)>
    where
        I: Iterator<Item = LexItem<'t>>,
    {
        todo!()
    }

    /// Read a vector
    pub fn read_vector<'t, I>(mut lex: I) -> MaltarResult<(Form<Val>, I)>
    where
        I: Iterator<Item = LexItem<'t>>,
    {
        todo!()
    }

    /// Read a map
    pub fn read_map<'t, I>(mut lex: I) -> MaltarResult<(Form<Val>, I)>
    where
        I: Iterator<Item = LexItem<'t>>,
    {
        todo!()
    }

    /// Read a set
    pub fn read_set<'t, I>(mut lex: I) -> MaltarResult<(Form<Val>, I)>
    where
        I: Iterator<Item = LexItem<'t>>,
    {
        todo!()
    }

    /// Read a anonymous function
    pub fn read_anon_func<'t, I>(mut lex: I) -> MaltarResult<(Form<Val>, I)>
    where
        I: Iterator<Item = LexItem<'t>>,
    {
        todo!()
    }

    /// Read a token as an atom
    pub fn read_atom<'t>(token: Token<'t>) -> MaltarResult<Form<Val>> {
        match token {
            Token::Character(_) => todo!(),
            Token::StringTok(_) => todo!(),
            Token::Number(_) => todo!(),
            Token::Keyword(_) => todo!(),
            _ => todo!(),
        }
    }

    pub fn eval(&self) -> MaltarResult {
        todo!()
    }
}
