use reader::{MalType, ParseError};
use rustyline::{error::ReadlineError, DefaultEditor};

pub(crate) mod reader {
    use std::{collections::VecDeque, fmt::Display};

    use logos::Logos;

    #[derive(Logos, Clone, Debug, PartialEq)]
    #[logos(skip r"[ \t\n\f]+")]
    enum Token<'t> {
        #[token("(")]
        OpenParen,
        #[token(")")]
        CloseParen,
        #[token("[")]
        OpenBracket,
        #[token("]")]
        CloseBracket,
        #[token("{")]
        OpenBrace,
        #[token("}")]
        CloseBrace,
        #[token("'")]
        Quote,
        #[token("`")]
        Quasiquote,
        #[token("~")]
        Unquote,
        #[token("@")]
        Deref,
        #[token("^")]
        Meta,

        // #[regex(r"[\[\]{}()'`~^@]")]
        // SingleTok(&'t str),
        #[regex(r#""(?:\\.|[^\\"])*"?"#)]
        StringTok(&'t str),

        #[regex(r";.*")]
        Comment(&'t str),

        #[regex(r#"[^\s\[\]{}('"`,;~@)]*"#)]
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
        fn is_atom(&self) -> bool {
            matches!(self, Token::Atom(_))
        }
        fn is_comment(&self) -> bool {
            matches!(self, Token::Comment(_))
        }
    }

    #[derive(PartialEq, Clone, Debug, PartialOrd)]
    pub enum MalType {
        Nil,
        True,
        False,
        Quote(Box<MalType>),
        Quasiquote(Box<MalType>),
        Unquote(Box<MalType>),
        SpliceUnquote(Box<MalType>),
        Deref(Box<MalType>),
        Meta(Vec<MalType>),
        Number(f64),
        Keyword(String),
        Symbol(String),
        String(String),
        List(Vec<MalType>),
        Vector(Vec<MalType>),
        Map(Vec<(MalType, MalType)>),
    }

    impl Display for MalType {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                MalType::Quote(q) => f.write_str(&format!("(quote {q})")),
                MalType::Unquote(q) => f.write_str(&format!("(unquote {q})")),
                MalType::Quasiquote(q) => f.write_str(&format!("(quasiquote {q})")),
                MalType::SpliceUnquote(q) => f.write_str(&format!("(splice-unquote {q})")),
                MalType::Deref(d) => f.write_str(&format!("(deref {d})")),
                MalType::Number(n) => f.write_str(&n.to_string()),
                MalType::Keyword(k) => f.write_str(k),
                MalType::Symbol(s) => f.write_str(s),
                MalType::Nil => f.write_str("nil"),
                MalType::True => f.write_str("true"),
                MalType::False => f.write_str("false"),
                MalType::String(s) => f.write_str(s),
                MalType::Meta(m) => f.write_str(&format!(
                    "(with-meta {})",
                    m.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                MalType::List(l) => f.write_str(&format!(
                    "({})",
                    l.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                MalType::Vector(v) => f.write_str(&format!(
                    "[{}]",
                    v.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                MalType::Map(m) => f.write_str(&format!(
                    "{{{}}}",
                    m.iter()
                        .map(|(k, v)| format!("{} {}", k, v))
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
            }
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq)]
    #[non_exhaustive]
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
                _ => todo!(),
            }
        }
    }

    pub fn read_str(input: &str) -> Result<Box<MalType>, ParseError> {
        let mut lexed_tokens = tokenize(input);
        let (expr, _rem) = read_form(&mut lexed_tokens)?;
        Ok(Box::new(expr))
    }
    fn tokenize<'t>(input: &'t str) -> VecDeque<Token<'t>> {
        Box::new(Token::lexer(input).filter_map(|res: Result<Token<'t>, ()>| res.ok()))
            .filter(|tok| !tok.is_comment())
            // .map(|tok| tok.to_string())
            .collect()
    }

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

    fn check_string(s: &str) -> bool {
        s.chars().fold((true, false), |acc, c| match (c, acc) {
            ('\"', (quote_open, false)) => (!quote_open, false),
            ('\\', (quote_open, false)) => (quote_open, true),
            (_c, (quote_open, true)) => (quote_open, false),
            _ => acc,
        }) == (true, false)
    }

    fn read_atom<'t>(
        lex_list: &'t mut VecDeque<Token<'t>>,
    ) -> Result<(MalType, &'t mut VecDeque<Token<'t>>), ParseError> {
        if let Some(token) = lex_list.pop_front() {
            match token {
                Token::StringTok(string) => {
                    if string.len() > 1 && string.ends_with('\"') && check_string(string) {
                        Ok((MalType::String(string.to_string()), lex_list))
                    } else {
                        Err(ParseError::UnbalancedParen)
                    }
                }
                Token::Atom(atom) => {
                    if let Ok(num) = atom.parse::<f64>() {
                        Ok((MalType::Number(num), lex_list))
                    } else {
                        match atom {
                            "nil" => Ok((MalType::Nil, lex_list)),
                            "true" => Ok((MalType::True, lex_list)),
                            "false" => Ok((MalType::False, lex_list)),
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
    use crate::step1::Ast;

    pub fn pr_str(ast: Ast) -> String {
        ast.expr.to_string()
    }
}

pub struct Ast {
    pub expr: MalType,
}
enum ReplError {
    ReadlineError(ReadlineError),
    ParseError(ParseError),
}

fn read(rl: &mut DefaultEditor) -> Result<Ast, ReplError> {
    let line = rl.readline("user> ").map_err(ReplError::ReadlineError)?;
    rl.add_history_entry(line.clone())
        .map_err(ReplError::ReadlineError)?;
    let expr = *reader::read_str(&line).map_err(ReplError::ParseError)?;
    Ok(Ast { expr })
}

fn eval(ast: Ast) -> Ast {
    ast
}

fn print(value: Ast) {
    println!("{}", printer::pr_str(value))
}

fn rep(rl: &mut DefaultEditor) -> Result<(), ReplError> {
    print(eval(read(rl)?));
    Ok(())
}

pub fn main() -> rustyline::Result<()> {
    let mut rl = DefaultEditor::new()?;
    loop {
        if let Err(err) = rep(&mut rl) {
            match err {
                ReplError::ReadlineError(ReadlineError::Eof | ReadlineError::Interrupted) => break,
                ReplError::ReadlineError(err) => {
                    println!("{}", err);
                    break;
                }
                ReplError::ParseError(ParseError::UnbalancedParen) => {
                    println!("Unbalanced Paren");
                    break;
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
    use super::*;
    use test_case::test_case;

    #[test_case(r#"1"#, r#"1"# ; r#"Testing read of numbers"#)]
    #[test_case(r#"7"#, r#"7"# ; r#"Test 1: 7 => 7"#)]
    #[test_case(r#"  7"#, r#"7"# ; r#"Test 2:   7 => 7"#)]
    #[test_case(r#"-123"#, r#"-123"# ; r#"Test 3: -123 => -123"#)]
    #[test_case(r#"+"#, r#"+"# ; r#"Testing read of symbols"#)]
    #[test_case(r#"abc"#, r#"abc"# ; r#"Test 4: abc => abc"#)]
    #[test_case(r#"   abc"#, r#"abc"# ; r#"Test 5:    abc => abc"#)]
    #[test_case(r#"abc5"#, r#"abc5"# ; r#"Test 6: abc5 => abc5"#)]
    #[test_case(r#"abc-def"#, r#"abc-def"# ; r#"Test 7: abc-def => abc-def"#)]
    #[test_case(r#"-"#, r#"-"# ; r#"Testing non-numbers starting with a dash."#)]
    #[test_case(r#"-abc"#, r#"-abc"# ; r#"Test 8: -abc => -abc"#)]
    #[test_case(r#"->>"#, r#"->>"# ; r#"Test 9: ->> => ->>"#)]
    #[test_case(r#"(+ 1 2)"#, r#"(+ 1 2)"# ; r#"Testing read of lists"#)]
    #[test_case(r#"()"#, r#"()"# ; r#"Test 10: () => ()"#)]
    #[test_case(r#"( )"#, r#"()"# ; r#"Test 11: ( ) => ()"#)]
    #[test_case(r#"(nil)"#, r#"(nil)"# ; r#"Test 12: (nil) => (nil)"#)]
    #[test_case(r#"((3 4))"#, r#"((3 4))"# ; r#"Test 13: ((3 4)) => ((3 4))"#)]
    #[test_case(r#"(+ 1 (+ 2 3))"#, r#"(+ 1 (+ 2 3))"# ; r#"Test 14: (+ 1 (+ 2 3)) => (+ 1 (+ 2 3))"#)]
    #[test_case(r#"  ( +   1   (+   2 3   )   )"#, r#"(+ 1 (+ 2 3))"# ; r#"Test 15:   ( +   1   (+   2 3   )   ) => (+ 1 (+ 2 3))"#)]
    #[test_case(r#"(* 1 2)"#, r#"(* 1 2)"# ; r#"Test 16: (* 1 2) => (* 1 2)"#)]
    #[test_case(r#"(** 1 2)"#, r#"(** 1 2)"# ; r#"Test 17: (** 1 2) => (** 1 2)"#)]
    #[test_case(r#"(* -3 6)"#, r#"(* -3 6)"# ; r#"Test 18: (* -3 6) => (* -3 6)"#)]
    #[test_case(r#"(()())"#, r#"(() ())"# ; r#"Test 19: (()()) => (() ())"#)]
    #[test_case(r#"(1 2, 3,,,,),,"#, r#"(1 2 3)"# ; r#"Test commas as whitespace"#)]
    #[test_case(r#"nil"#, r#"nil"# ; r#"Testing read of nil/true/false"#)]
    #[test_case(r#"true"#, r#"true"# ; r#"Test 20: true => true"#)]
    #[test_case(r#"false"#, r#"false"# ; r#"Test 21: false => false"#)]
    #[test_case(r#""abc""#, r#""abc""# ; r#"Testing read of strings"#)]
    #[test_case(r#"   "abc""#, r#""abc""# ; r#"Test 22:    "abc" => "abc""#)]
    #[test_case(r#""abc (with parens)""#, r#""abc (with parens)""# ; r#"Test 23: "abc (with parens)" => "abc (with parens)""#)]
    #[test_case(r#""abc\"def""#, r#""abc\"def""# ; r#"Test 24: "abc\"def" => "abc\"def""#)]
    #[test_case(r#""""#, r#""""# ; r#"Test 25: "" => """#)]
    #[test_case(r#""\\""#, r#""\\""# ; r#"Test 26: "\\" => "\\""#)]
    #[test_case(r#""\\\\\\\\\\\\\\\\\\""#, r#""\\\\\\\\\\\\\\\\\\""# ; r#"Test 27: "\\\\\\\\\\\\\\\\\\" => "\\\\\\\\\\\\\\\\\\""#)]
    #[test_case(r#""&""#, r#""&""# ; r#"Test 28: "&" => "&""#)]
    #[test_case(r#""'""#, r#""'""# ; r#"Test 29: "'" => "'""#)]
    #[test_case(r#""(""#, r#""(""# ; r#"Test 30: "(" => "(""#)]
    #[test_case(r#"")""#, r#"")""# ; r#"Test 31: ")" => ")""#)]
    #[test_case(r#""*""#, r#""*""# ; r#"Test 32: "*" => "*""#)]
    #[test_case(r#""+""#, r#""+""# ; r#"Test 33: "+" => "+""#)]
    #[test_case(r#"",""#, r#"",""# ; r#"Test 34: "," => ",""#)]
    #[test_case(r#""-""#, r#""-""# ; r#"Test 35: "-" => "-""#)]
    #[test_case(r#""/""#, r#""/""# ; r#"Test 36: "/" => "/""#)]
    #[test_case(r#"":""#, r#"":""# ; r#"Test 37: ":" => ":""#)]
    #[test_case(r#"";""#, r#"";""# ; r#"Test 38: ";" => ";""#)]
    #[test_case(r#""<""#, r#""<""# ; r#"Test 39: "<" => "<""#)]
    #[test_case(r#""=""#, r#""=""# ; r#"Test 40: "=" => "=""#)]
    #[test_case(r#"">""#, r#"">""# ; r#"Test 41: ">" => ">""#)]
    #[test_case(r#""?""#, r#""?""# ; r#"Test 42: "?" => "?""#)]
    #[test_case(r#""@""#, r#""@""# ; r#"Test 43: "@" => "@""#)]
    #[test_case(r#""[""#, r#""[""# ; r#"Test 44: "[" => "[""#)]
    #[test_case(r#""]""#, r#""]""# ; r#"Test 45: "]" => "]""#)]
    #[test_case(r#""^""#, r#""^""# ; r#"Test 46: "^" => "^""#)]
    #[test_case(r#""_""#, r#""_""# ; r#"Test 47: "_" => "_""#)]
    #[test_case(r#""`""#, r#""`""# ; r#"Test 48: "`" => "`""#)]
    #[test_case(r#""{""#, r#""{""# ; r#"Test 49: "{" => "{""#)]
    #[test_case(r#""}""#, r#""}""# ; r#"Test 50: "}" => "}""#)]
    #[test_case(r#""~""#, r#""~""# ; r#"Test 51: "~" => "~""#)]
    #[test_case(r#""!""#, r#""!""# ; r#"Test 52: "!" => "!""#)]
    #[test_case(r#"(1 2"#, r#"(EOF|end of input|unbalanced)"# ; r#"Testing reader errors"#)]
    #[test_case(r#"[1 2"#, r#"(EOF|end of input|unbalanced)"# ; r#"Test 53: [1 2 => (EOF|end of input|unbalanced)"#)]
    #[test_case(r#""abc"#, r#"(EOF|end of input|unbalanced)"# ; r#"Test 54: "abc => (EOF|end of input|unbalanced)"#)]
    #[test_case(r#"""#, r#"(EOF|end of input|unbalanced)"# ; r#"Test 55: " => (EOF|end of input|unbalanced)"#)]
    #[test_case(r#""\""#, r#"(EOF|end of input|unbalanced)"# ; r#"Test 56: "\" => (EOF|end of input|unbalanced)"#)]
    #[test_case(r#""\\\\\\\\\\\\\\\\\\\""#, r#"(EOF|end of input|unbalanced)"# ; r#"Test 57: "\\\\\\\\\\\\\\\\\\\" => (EOF|end of input|unbalanced)"#)]
    #[test_case(r#"(1 "abc"#, r#"(EOF|end of input|unbalanced)"# ; r#"Test 58: (1 "abc => (EOF|end of input|unbalanced)"#)]
    #[test_case(r#"(1 "abc""#, r#"(EOF|end of input|unbalanced)"# ; r#"Test 59: (1 "abc" => (EOF|end of input|unbalanced)"#)]
    #[test_case(r#"'1"#, r#"(quote 1)"# ; r#"Testing read of quoting"#)]
    #[test_case(r#"'(1 2 3)"#, r#"(quote (1 2 3))"# ; r#"Test 60: '(1 2 3) => (quote (1 2 3))"#)]
    #[test_case(r#"`1"#, r#"(quasiquote 1)"# ; r#"Test 61: `1 => (quasiquote 1)"#)]
    #[test_case(r#"`(1 2 3)"#, r#"(quasiquote (1 2 3))"# ; r#"Test 62: `(1 2 3) => (quasiquote (1 2 3))"#)]
    #[test_case(r#"~1"#, r#"(unquote 1)"# ; r#"Test 63: ~1 => (unquote 1)"#)]
    #[test_case(r#"~(1 2 3)"#, r#"(unquote (1 2 3))"# ; r#"Test 64: ~(1 2 3) => (unquote (1 2 3))"#)]
    #[test_case(r#"`(1 ~a 3)"#, r#"(quasiquote (1 (unquote a) 3))"# ; r#"Test 65: `(1 ~a 3) => (quasiquote (1 (unquote a) 3))"#)]
    #[test_case(r#"~@(1 2 3)"#, r#"(splice-unquote (1 2 3))"# ; r#"Test 66: ~@(1 2 3) => (splice-unquote (1 2 3))"#)]
    #[test_case(r#":kw"#, r#":kw"# ; r#"Testing keywords"#)]
    #[test_case(r#"(:kw1 :kw2 :kw3)"#, r#"(:kw1 :kw2 :kw3)"# ; r#"Test 67: (:kw1 :kw2 :kw3) => (:kw1 :kw2 :kw3)"#)]
    #[test_case(r#"[+ 1 2]"#, r#"[+ 1 2]"# ; r#"Testing read of vectors"#)]
    #[test_case(r#"[]"#, r#"[]"# ; r#"Test 68: [] => []"#)]
    #[test_case(r#"[ ]"#, r#"[]"# ; r#"Test 69: [ ] => []"#)]
    #[test_case(r#"[[3 4]]"#, r#"[[3 4]]"# ; r#"Test 70: [[3 4]] => [[3 4]]"#)]
    #[test_case(r#"[+ 1 [+ 2 3]]"#, r#"[+ 1 [+ 2 3]]"# ; r#"Test 71: [+ 1 [+ 2 3]] => [+ 1 [+ 2 3]]"#)]
    #[test_case(r#"  [ +   1   [+   2 3   ]   ]"#, r#"[+ 1 [+ 2 3]]"# ; r#"Test 72:   [ +   1   [+   2 3   ]   ] => [+ 1 [+ 2 3]]"#)]
    #[test_case(r#"([])"#, r#"([])"# ; r#"Test 73: ([]) => ([])"#)]
    #[test_case(r#"{}"#, r#"{}"# ; r#"Testing read of hash maps"#)]
    #[test_case(r#"{ }"#, r#"{}"# ; r#"Test 74: { } => {}"#)]
    #[test_case(r#"{"abc" 1}"#, r#"{"abc" 1}"# ; r#"Test 75: {"abc" 1} => {"abc" 1}"#)]
    #[test_case(r#"{"a" {"b" 2}}"#, r#"{"a" {"b" 2}}"# ; r#"Test 76: {"a" {"b" 2}} => {"a" {"b" 2}}"#)]
    #[test_case(r#"{"a" {"b" {"c" 3}}}"#, r#"{"a" {"b" {"c" 3}}}"# ; r#"Test 77: {"a" {"b" {"c" 3}}} => {"a" {"b" {"c" 3}}}"#)]
    #[test_case(r#"{  "a"  {"b"   {  "cde"     3   }  }}"#, r#"{"a" {"b" {"cde" 3}}}"# ; r#"Test 78: {  "a"  {"b"   {  "cde"     3   }  }} => {"a" {"b" {"cde" 3}}}"#)]
    #[test_case(r#"{"a1" 1 "a2" 2 "a3" 3}"#, r#"{"a1" 1 "a2" 2 "a3" 3}"# ; r#"Test 79: {"a1" 1 "a2" 2 "a3" 3} => a([1-3])" \1 "a(?!\1)([1-3])" \2 "a(?!\1)(?!\2)([1-3])" \"#)]
    #[test_case(r#"{  :a  {:b   {  :cde     3   }  }}"#, r#"{:a {:b {:cde 3}}}"# ; r#"Test 80: {  :a  {:b   {  :cde     3   }  }} => {:a {:b {:cde 3}}}"#)]
    #[test_case(r#"{"1" 1}"#, r#"{"1" 1}"# ; r#"Test 81: {"1" 1} => {"1" 1}"#)]
    #[test_case(r#"({})"#, r#"({})"# ; r#"Test 82: ({}) => ({})"#)]
    #[test_case(r#"^{"a" 1} [1 2 3]"#, r#"(with-meta [1 2 3] {"a" 1})"# ; r#"Testing read of ^/metadata"#)]
    #[test_case(r#"1 ; comment after expression"#, r#"1"# ; r#"Testing read of comments whole line comment (not an exception)"#)]
    #[test_case(r#"1; comment after expression"#, r#"1"# ; r#"Test 83: 1; comment after expression => 1"#)]
    #[test_case(r#"@a"#, r#"(deref a)"# ; r#"Testing read of @/deref"#)]
    #[test_case(r#""\n""#, r#""\n""# ; r#"Non alphanumerice characters in strings"#)]
    #[test_case(r##""#""##, r##""#""## ; r##"Test 84: "#" => "#""##)]
    #[test_case(r#""$""#, r#""$""# ; r#"Test 85: "$" => "$""#)]
    #[test_case(r#""%""#, r#""%""# ; r#"Test 86: "%" => "%""#)]
    #[test_case(r#"".""#, r#"".""# ; r#"Test 87: "." => ".""#)]
    #[test_case(r#""\\""#, r#""\\""# ; r#"Test 88: "\\" => "\\""#)]
    #[test_case(r#""|""#, r#""|""# ; r#"Test 89: "|" => "|""#)]
    #[test_case(r#"1;!"#, r#"1"# ; r#"Non alphanumeric characters in comments"#)]
    #[test_case(r#"1;""#, r#"1"# ; r#"Test 90: 1;" => 1"#)]
    #[test_case(r##"1;#"##, r#"1"# ; r##"Test 91: 1;# => 1"##)]
    #[test_case(r#"1;$"#, r#"1"# ; r#"Test 92: 1;$ => 1"#)]
    #[test_case(r#"1;%"#, r#"1"# ; r#"Test 93: 1;% => 1"#)]
    #[test_case(r#"1;'"#, r#"1"# ; r#"Test 94: 1;' => 1"#)]
    #[test_case(r#"1;\"#, r#"1"# ; r#"Test 95: 1;\ => 1"#)]
    #[test_case(r#"1;\\"#, r#"1"# ; r#"Test 96: 1;\\ => 1"#)]
    #[test_case(r#"1;\\\"#, r#"1"# ; r#"Test 97: 1;\\\ => 1"#)]
    #[test_case(r#"1;`"#, r#"1"# ; r#"Test 98: 1;` => 1"#)]
    #[test_case(r#"1; &()*+,-./:;<=>?@[]^_{|}~"#, r#"1"# ; r#"Test 99: 1; &()*+,-./:;<=>?@[]^_{|}~ => 1"#)]
    fn step_1_tester(input: &str, output: &str) {
        match reader::read_str(input) {
            Ok(expr) => assert_eq!(printer::pr_str(eval(Ast { expr: *expr })), output),
            Err(err) => assert_eq!(err.to_string(), output),
        }
    }
}
