use crate::{new_env::Env, types::ErrorType};

use super::lexer::{NewToken, PunctuationType, SpecialReaderSymbol};

const DISPATCH: NewToken = NewToken::ReaderSymbol(SpecialReaderSymbol::Dispatch);
const OPEN_PAREN: NewToken = NewToken::OpenPunctuation(PunctuationType::Parenthesis);

/// The form
/// Adapted from Clojure
///
/// Note: Parser is LL(1)
pub enum Form<T> {
    Def {},
    Do(Vec<T>),
    Let {
        bindings: Vec<String>,
        exprs: Vec<T>,
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

#[derive(Debug, Clone)]
pub enum ParseError {}

type R<T, K> = Result<(Form<T>, K), ParseError>;

impl<T> Form<T> {
    // pub fn read_form<'t>(
    //     mut lex_iter: impl Iterator<Item = NewToken>,
    // ) -> R<T, impl Iterator<Item = NewToken>> {
    //     match lex_iter.next() {
    //         Some(DISPATCH) => todo!(),
    //         Some(OPEN_PAREN) => todo!(),
    //         Some(_) => todo!(),
    //         None => todo!(),
    //     }
    // }

    // pub fn read_list<'t>(lex_list: Input<'t>) -> Output<'t, Self> {
    //     match lex_list {
    //         [NewToken::OpenPunctuation(Parenthesis), rest @ ..] => todo!(),
    //         [] => todo!(),
    //         _ => todo!(),
    //     }
    // }

    pub fn eval(&self, env: &Env) -> Result<T, ErrorType> {
        todo!()
    }
}
