//! Module for parsing into forms
use im::Vector;
use string_interner::symbol::SymbolUsize;

use crate::types::{
    error::{Error, LexResult, ParseError},
    value::MaltarValue,
    MaltarResult,
};

use super::lexer::{tokenize, Token};

pub struct FnPart<Val>
where
    Val: Into<MaltarValue<Val>> + Clone + std::hash::Hash + Eq + Ord,
{
    params: Vec<String>,
    exprs: Vec<Val>,
}
/// Form representation an evaulatable representation of the types
pub enum Form<Val>
where
    Val: Into<MaltarValue<Val>> + Clone + std::hash::Hash + Eq + Ord,
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

impl<Val> Form<Val>
where
    Val: Into<MaltarValue<Val>> + Clone + std::hash::Hash + Eq + Ord,
{
    pub fn read_string(input: &str) -> MaltarResult<Form<Val>> {
        let tokens = tokenize(input);
        let (form, remaining) = Form::read_form(tokens)?;
        Ok(form)
    }
    pub fn read_form<'t, I>(mut lex: I) -> MaltarResult<(Form<Val>, I)>
    where
        I: Iterator<Item = LexResult<Token<'t>>>,
    {
        lex.next()
            .ok_or(Error::Custom("Unexpected EOF".to_string()))
            .and_then(|res| {
                res.map_err(|err| err.into()).and_then(|tok| match tok {
                    _ => todo!(),
                })
            })
    }

    pub fn eval(&self) -> MaltarResult {
        todo!()
    }
}
