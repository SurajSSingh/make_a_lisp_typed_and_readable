use im::Vector;
use logos::Span;

use crate::{
    new_env::Env,
    types::{
        error::{ErrorType, EvalResult, ParseResult, ProgramResult},
        SpannedValue,
    },
};

use super::lexer::{NewToken, PunctuationType, SpecialReaderSymbol};

const DISPATCH: NewToken = NewToken::ReaderSymbol(SpecialReaderSymbol::Dispatch);
const OPEN_PAREN: NewToken = NewToken::OpenPunctuation(PunctuationType::Parenthesis);
const OPEN_BRACKET: NewToken = NewToken::OpenPunctuation(PunctuationType::Bracket);
const OPEN_BRACE: NewToken = NewToken::OpenPunctuation(PunctuationType::Brace);

/// The form
/// Adapted from Clojure
///
/// Note: Parser is LL(1)
pub enum Form<T> {
    Def {},
    Do(Vector<SpannedValue>),
    Let {
        bindings: Vector<String>,
        exprs: Vector<SpannedValue>,
    },
    Loop {
        bindings: Vec<String>,
        exprs: Vec<T>,
    },
    If {
        condition_expr: T,
        true_expr: T,
        false_expr: Option<T>,
    },
    Quote(Box<Form<T>>),
    Try {
        try_expr: Vec<T>,
        catch_expr: Vec<T>,
        finally_expr: Option<T>,
    },
    Throw(T),
    Normal(T),
}

type ParseToken = (NewToken, Span);

impl<T> Form<T> {
    /// Read from a string input and try to produce a new expression
    pub fn read_from_string(input: &str) -> ProgramResult<Form<T>> {
        let lex = NewToken::tokenize(input)
            .map_err(ErrorType::Lex)?
            .into_iter();
        let final_form = Form::<T>::read_form(lex).map_err(ErrorType::Parse)?;
        Ok(final_form)
    }

    pub fn read_form<I>(mut lex_iter: I) -> ParseResult<Form<T>>
    where
        I: Iterator<Item = ParseToken>,
    {
        match lex_iter.next() {
            Some((DISPATCH, _)) => match lex_iter.next() {
                Some((OPEN_BRACE, _)) => Form::read_set(lex_iter),
                Some(_) => todo!(),
                None => todo!(),
            },
            Some((OPEN_PAREN, _)) => Form::read_list(lex_iter),
            Some((OPEN_BRACKET, _)) => Form::read_vector(lex_iter),
            Some((OPEN_BRACE, _)) => Form::read_map(lex_iter),
            Some(_) => todo!(),
            None => todo!(),
        }
    }

    pub fn read_list<I>(mut lex_iter: I) -> ParseResult<Form<T>>
    where
        I: Iterator<Item = ParseToken>,
    {
        todo!()
    }

    pub fn read_vector<I>(mut lex_iter: I) -> ParseResult<Form<T>>
    where
        I: Iterator<Item = ParseToken>,
    {
        todo!()
    }

    pub fn read_map<I>(mut lex_iter: I) -> ParseResult<Form<T>>
    where
        I: Iterator<Item = ParseToken>,
    {
        todo!()
    }

    pub fn read_set<I>(mut lex_iter: I) -> ParseResult<Form<T>>
    where
        I: Iterator<Item = ParseToken>,
    {
        todo!()
    }
    pub fn read_atom<I>(mut lex_iter: I) -> ParseResult<Form<T>>
    where
        I: Iterator<Item = ParseToken>,
    {
        todo!()
    }

    pub fn read_if<I>(mut lex_iter: I) -> ParseResult<Form<T>>
    where
        I: Iterator<Item = ParseToken>,
    {
        todo!()
    }

    /// Evaluates the form with the given environment and returns a result
    pub fn eval(&self, env: &Env) -> EvalResult<T> {
        todo!()
    }
}
