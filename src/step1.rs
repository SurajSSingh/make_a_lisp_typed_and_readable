use reader::{MalType, ParseError};
use rustyline::{error::ReadlineError, DefaultEditor};

pub(crate) mod reader {
    use std::{collections::VecDeque, fmt::Display, iter::once};

    use logos::Logos;

    #[derive(Logos, Clone, Debug, PartialEq)]
    #[logos(skip r"[ \t\n\f]+")]
    enum Token<'t> {
        #[token("~@")]
        SpecialTok,

        #[regex(r"[\[\]{}()'`~^@]")]
        SingleTok(&'t str),

        #[regex(r#""(?:\\.|[^\\"])*"?"#)]
        StringTok(&'t str),

        #[regex(r";.*")]
        Comment(&'t str),

        #[regex(r#"[^\s\[\]{}('"`,;)]*"#)]
        Atom(&'t str),
    }

    impl<'t> Display for Token<'t> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Token::SpecialTok => f.write_str("~@"),
                Token::SingleTok(tok) => f.write_str(tok),
                Token::StringTok(str) => f.write_str(str),
                Token::Comment(com) => f.write_str(com),
                Token::Atom(atm) => f.write_str(atm),
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

    #[derive(PartialEq, Clone, Debug)]
    pub enum MalType {
        List(Vec<MalType>),
        Number(f64),
        Symbol(String),
    }

    impl<'m> Display for MalType {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                MalType::List(l) => f.write_str(&format!(
                    "({})",
                    l.into_iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                MalType::Number(n) => f.write_str(&n.to_string()),
                MalType::Symbol(s) => f.write_str(s),
            }
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq)]
    pub enum ParseError {
        EOF,
        UnbalancedParen,
    }

    pub fn read_str<'t>(input: &'t str) -> Result<Box<MalType>, ParseError> {
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
                Token::SingleTok("(") => {
                    lex_list.pop_front();
                    Ok(read_list(lex_list)?)
                }
                _ => Ok(read_atom(lex_list)?),
            }
        } else {
            Err(ParseError::EOF)
        }
    }

    fn read_list<'t>(
        lex_list: &'t mut VecDeque<Token<'t>>,
    ) -> Result<(MalType, &'t mut VecDeque<Token<'t>>), ParseError> {
        let mut list = Vec::new();
        let mut rem = lex_list;
        while let Some(token) = rem.get(0) {
            match token {
                Token::SingleTok(")") => {
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
    fn read_atom<'t>(
        lex_list: &'t mut VecDeque<Token<'t>>,
    ) -> Result<(MalType, &'t mut VecDeque<Token<'t>>), ParseError> {
        if let Some(Token::Atom(atom)) = lex_list.pop_front() {
            if let Ok(num) = atom.parse::<f64>() {
                Ok((MalType::Number(num), lex_list))
            } else {
                Ok((MalType::Symbol(atom.to_string()), lex_list))
            }
        } else {
            Err(ParseError::EOF)
        }
    }
}

pub(crate) mod printer {
    use crate::step1::AST;

    pub fn pr_str(ast: AST) -> String {
        ast.expr.to_string()
    }
}

pub struct AST {
    pub expr: MalType,
}
enum ReplError {
    ReadlineError(ReadlineError),
    ParseError(ParseError),
}

fn read(rl: &mut DefaultEditor) -> Result<AST, ReplError> {
    let line = rl.readline("user> ").map_err(ReplError::ReadlineError)?;
    rl.add_history_entry(line.clone())
        .map_err(ReplError::ReadlineError)?;
    let expr = *reader::read_str(&line).map_err(ReplError::ParseError)?;
    Ok(AST { expr })
}

fn eval(ast: AST) -> AST {
    ast
}

fn print(value: AST) {
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

    #[test_case("1", "1" ; "Testing read of numbers")]
    #[test_case("7", "7" ; "Test #1: 7 => 7")]
    #[test_case("  7", "7" ; "Test #2:   7 => 7")]
    #[test_case("-123", "-123" ; "Test #3: -123 => -123")]
    #[test_case("+", "+" ; "Testing read of symbols")]
    #[test_case("abc", "abc" ; "Test #4: abc => abc")]
    #[test_case("   abc", "abc" ; "Test #5:    abc => abc")]
    #[test_case("abc5", "abc5" ; "Test #6: abc5 => abc5")]
    #[test_case("abc-def", "abc-def" ; "Test #7: abc-def => abc-def")]
    #[test_case("-", "-" ; "Testing non-numbers starting with a dash.")]
    #[test_case("-abc", "-abc" ; "Test #8: -abc => -abc")]
    #[test_case("->>", "->>" ; "Test #9: ->> => ->>")]
    #[test_case("(+ 1 2)", "(+ 1 2)" ; "Testing read of lists")]
    #[test_case("()", "()" ; "Test #10: () => ()")]
    #[test_case("( )", "()" ; "Test #11: ( ) => ()")]
    #[test_case("(nil)", "(nil)" ; "Test #12: (nil) => (nil)")]
    #[test_case("((3 4))", "((3 4))" ; "Test #13: ((3 4)) => ((3 4))")]
    #[test_case("(+ 1 (+ 2 3))", "(+ 1 (+ 2 3))" ; "Test #14: (+ 1 (+ 2 3)) => (+ 1 (+ 2 3))")]
    #[test_case("  ( +   1   (+   2 3   )   )", "(+ 1 (+ 2 3))" ; "Test #15:   ( +   1   (+   2 3   )   ) => (+ 1 (+ 2 3))")]
    #[test_case("(* 1 2)", "(* 1 2)" ; "Test #16: (* 1 2) => (* 1 2)")]
    #[test_case("(** 1 2)", "(** 1 2)" ; "Test #17: (** 1 2) => (** 1 2)")]
    #[test_case("(* -3 6)", "(* -3 6)" ; "Test #18: (* -3 6) => (* -3 6)")]
    #[test_case("(()())", "(() ())" ; "Test #19: (()()) => (() ())")]
    #[test_case("(1 2, 3,,,,),,", "(1 2 3)" ; "Test commas as whitespace")]
    #[test_case(";;", "(1 2 3)" ; "Test #20: ;; => (1 2 3)")]
    #[test_case("nil", "nil" ; "Testing read of nil/true/false")]
    #[test_case("true", "true" ; "Test #21: true => true")]
    #[test_case("false", "false" ; "Test #22: false => false")]
    #[test_case("\"abc\"", "\"abc\"" ; "Testing read of strings")]
    #[test_case("   \"abc\"", "\"abc\"" ; "Test #23:    \"abc\" => \"abc\"")]
    #[test_case("\"abc (with parens)\"", "\"abc (with parens)\"" ; "Test #24: \"abc (with parens)\" => \"abc (with parens)\"")]
    // #[test_case("\"abc\\"def\"", "\"abc\\"def\"" ; "Test #25: \"abc\\"def\" => \"abc\\"def\"")]
    #[test_case("\"\"", "\"\"" ; "Test #26: \"\" => \"\"")]
    #[test_case("\"\\\"", "\"\\\"" ; "Test #27: \"\\\" => \"\\\"")]
    #[test_case("\"\\\\\\\\\\\\\\\\\\\"", "\"\\\\\\\\\\\\\\\\\\\"" ; "Test #28: \"\\\\\\\\\\\\\\\\\\\" => \"\\\\\\\\\\\\\\\\\\\"")]
    #[test_case("\"&\"", "\"&\"" ; "Test #29: \"&\" => \"&\"")]
    #[test_case("\"'\"", "\"'\"" ; "Test #30: \"'\" => \"'\"")]
    #[test_case("\"(\"", "\"(\"" ; "Test #31: \"(\" => \"(\"")]
    #[test_case("\")\"", "\")\"" ; "Test #32: \")\" => \")\"")]
    #[test_case("\"*\"", "\"*\"" ; "Test #33: \"*\" => \"*\"")]
    #[test_case("\"+\"", "\"+\"" ; "Test #34: \"+\" => \"+\"")]
    #[test_case("\",\"", "\",\"" ; "Test #35: \",\" => \",\"")]
    #[test_case("\"-\"", "\"-\"" ; "Test #36: \"-\" => \"-\"")]
    #[test_case("\"/\"", "\"/\"" ; "Test #37: \"/\" => \"/\"")]
    #[test_case("\":\"", "\":\"" ; "Test #38: \":\" => \":\"")]
    #[test_case("\";\"", "\";\"" ; "Test #39: \";\" => \";\"")]
    #[test_case("\"<\"", "\"<\"" ; "Test #40: \"<\" => \"<\"")]
    #[test_case("\"=\"", "\"=\"" ; "Test #41: \"=\" => \"=\"")]
    #[test_case("\">\"", "\">\"" ; "Test #42: \">\" => \">\"")]
    #[test_case("\"?\"", "\"?\"" ; "Test #43: \"?\" => \"?\"")]
    #[test_case("\"@\"", "\"@\"" ; "Test #44: \"@\" => \"@\"")]
    #[test_case("\"[\"", "\"[\"" ; "Test #45: \"[\" => \"[\"")]
    #[test_case("\"]\"", "\"]\"" ; "Test #46: \"]\" => \"]\"")]
    #[test_case("\"^\"", "\"^\"" ; "Test #47: \"^\" => \"^\"")]
    #[test_case("\"_\"", "\"_\"" ; "Test #48: \"_\" => \"_\"")]
    #[test_case("\"`\"", "\"`\"" ; "Test #49: \"`\" => \"`\"")]
    #[test_case("\"{\"", "\"{\"" ; "Test #50: \"{\" => \"{\"")]
    #[test_case("\"}\"", "\"}\"" ; "Test #51: \"}\" => \"}\"")]
    #[test_case("\"~\"", "\"~\"" ; "Test #52: \"~\" => \"~\"")]
    #[test_case("\"!\"", "\"!\"" ; "Test #53: \"!\" => \"!\"")]
    #[test_case("(1 2", "\"!\"" ; "Testing reader errors")]
    #[test_case("[1 2", "\"!\"" ; "Test #54: [1 2 => \"!\"")]
    #[test_case("\"abc", "\"!\"" ; "Test #55: \"abc => \"!\"")]
    #[test_case("\"", "\"!\"" ; "Test #56: \" => \"!\"")]
    // #[test_case(r"\"\\"", "\"!\"" ; "Test #57: \"\\" => \"!\"")]
    // #[test_case(r"\"\\\\\\\\\\\\\\\\\\\\"", "\"!\"" ; "Test #58: \"\\\\\\\\\\\\\\\\\\\\" => \"!\"")]
    #[test_case("(1 \"abc", "\"!\"" ; "Test #59: (1 \"abc => \"!\"")]
    #[test_case("(1 \"abc\"", "\"!\"" ; "Test #60: (1 \"abc\" => \"!\"")]
    #[test_case("'1", "(quote 1)" ; "Testing read of quoting")]
    #[test_case("'(1 2 3)", "(quote (1 2 3))" ; "Test #61: '(1 2 3) => (quote (1 2 3))")]
    #[test_case("`1", "(quasiquote 1)" ; "Test #62: `1 => (quasiquote 1)")]
    #[test_case("`(1 2 3)", "(quasiquote (1 2 3))" ; "Test #63: `(1 2 3) => (quasiquote (1 2 3))")]
    #[test_case("~1", "(unquote 1)" ; "Test #64: ~1 => (unquote 1)")]
    #[test_case("~(1 2 3)", "(unquote (1 2 3))" ; "Test #65: ~(1 2 3) => (unquote (1 2 3))")]
    #[test_case("`(1 ~a 3)", "(quasiquote (1 (unquote a) 3))" ; "Test #66: `(1 ~a 3) => (quasiquote (1 (unquote a) 3))")]
    #[test_case("~@(1 2 3)", "(splice-unquote (1 2 3))" ; "Test #67: ~@(1 2 3) => (splice-unquote (1 2 3))")]
    #[test_case(":kw", ":kw" ; "Testing keywords")]
    #[test_case("(:kw1 :kw2 :kw3)", "(:kw1 :kw2 :kw3)" ; "Test #68: (:kw1 :kw2 :kw3) => (:kw1 :kw2 :kw3)")]
    #[test_case("[+ 1 2]", "[+ 1 2]" ; "Testing read of vectors")]
    #[test_case("[]", "[]" ; "Test #69: [] => []")]
    #[test_case("[ ]", "[]" ; "Test #70: [ ] => []")]
    #[test_case("[[3 4]]", "[[3 4]]" ; "Test #71: [[3 4]] => [[3 4]]")]
    #[test_case("[+ 1 [+ 2 3]]", "[+ 1 [+ 2 3]]" ; "Test #72: [+ 1 [+ 2 3]] => [+ 1 [+ 2 3]]")]
    #[test_case("  [ +   1   [+   2 3   ]   ]", "[+ 1 [+ 2 3]]" ; "Test #73:   [ +   1   [+   2 3   ]   ] => [+ 1 [+ 2 3]]")]
    #[test_case("([])", "([])" ; "Test #74: ([]) => ([])")]
    #[test_case("{}", "{}" ; "Testing read of hash maps")]
    #[test_case("{ }", "{}" ; "Test #75: { } => {}")]
    #[test_case("{\"abc\" 1}", "{\"abc\" 1}" ; "Test #76: {\"abc\" 1} => {\"abc\" 1}")]
    #[test_case("{\"a\" {\"b\" 2}}", "{\"a\" {\"b\" 2}}" ; "Test #77: {\"a\" {\"b\" 2}} => {\"a\" {\"b\" 2}}")]
    #[test_case("{\"a\" {\"b\" {\"c\" 3}}}", "{\"a\" {\"b\" {\"c\" 3}}}" ; "Test #78: {\"a\" {\"b\" {\"c\" 3}}} => {\"a\" {\"b\" {\"c\" 3}}}")]
    #[test_case("{  \"a\"  {\"b\"   {  \"cde\"     3   }  }}", "{\"a\" {\"b\" {\"cde\" 3}}}" ; "Test #79: {  \"a\"  {\"b\"   {  \"cde\"     3   }  }} => {\"a\" {\"b\" {\"cde\" 3}}}")]
    #[test_case("{\"a1\" 1 \"a2\" 2 \"a3\" 3}", "{\"a\" {\"b\" {\"cde\" 3}}}" ; "Test #80: {\"a1\" 1 \"a2\" 2 \"a3\" 3} => {\"a\" {\"b\" {\"cde\" 3}}}")]
    #[test_case("{  :a  {:b   {  :cde     3   }  }}", "{:a {:b {:cde 3}}}" ; "Test #81: {  :a  {:b   {  :cde     3   }  }} => {:a {:b {:cde 3}}}")]
    #[test_case("{\"1\" 1}", "{\"1\" 1}" ; "Test #82: {\"1\" 1} => {\"1\" 1}")]
    #[test_case("({})", "({})" ; "Test #83: ({}) => ({})")]
    #[test_case(" ;; whole line comment (not an exception)", "({})" ; "Testing read of comments")]
    #[test_case(";=>1", "({})" ; "Test #84: ;=>1 => ({})")]
    #[test_case(";=>1", "({})" ; "Test #85: ;=>1 => ({})")]
    #[test_case("@a", "(deref a)" ; "Testing read of @/deref")]
    #[test_case(";;", "(deref a)" ; "Test #86: ;; => (deref a)")]
    #[test_case("^{\"a\" 1} [1 2 3]", "(with-meta [1 2 3] {\"a\" 1})" ; "Testing read of ^/metadata")]
    #[test_case(";;; \t is not specified enough to be tested", "(with-meta [1 2 3] {\"a\" 1})" ; "Non alphanumerice characters in strings")]
    #[test_case(";=>\"\n\"", "(with-meta [1 2 3] {\"a\" 1})" ; "Test #87: ;=>\"\n\" => (with-meta [1 2 3] {\"a\" 1})")]
    #[test_case(";=>\"#\"", "(with-meta [1 2 3] {\"a\" 1})" ; "Test #88: ;=>\"#\" => (with-meta [1 2 3] {\"a\" 1})")]
    #[test_case(";=>\"$\"", "(with-meta [1 2 3] {\"a\" 1})" ; "Test #89: ;=>\"$\" => (with-meta [1 2 3] {\"a\" 1})")]
    #[test_case(";=>\"%\"", "(with-meta [1 2 3] {\"a\" 1})" ; "Test #90: ;=>\"%\" => (with-meta [1 2 3] {\"a\" 1})")]
    #[test_case(";=>\".\"", "(with-meta [1 2 3] {\"a\" 1})" ; "Test #91: ;=>\".\" => (with-meta [1 2 3] {\"a\" 1})")]
    #[test_case(";=>\"\\\"", "(with-meta [1 2 3] {\"a\" 1})" ; "Test #92: ;=>\"\\\" => (with-meta [1 2 3] {\"a\" 1})")]
    #[test_case(";=>\"|\"", "(with-meta [1 2 3] {\"a\" 1})" ; "Test #93: ;=>\"|\" => (with-meta [1 2 3] {\"a\" 1})")]
    #[test_case("1;!", "1" ; "Non alphanumeric characters in comments")]
    #[test_case("1;\"", "1" ; "Test #94: 1;\" => 1")]
    #[test_case("1;#", "1" ; "Test #95: 1;# => 1")]
    #[test_case("1;$", "1" ; "Test #96: 1;$ => 1")]
    #[test_case("1;%", "1" ; "Test #97: 1;% => 1")]
    #[test_case("1;'", "1" ; "Test #98: 1;' => 1")]
    #[test_case(r"1;\", "1" ; "Test #99: 1; => 1")]
    #[test_case(r"1;\\", "1" ; "Test #100: 1;\\ => 1")]
    #[test_case(r"1;\\\", "1" ; "Test #101: 1;\\ => 1")]
    #[test_case("1;`", "1" ; "Test #102: 1;` => 1")]
    #[test_case("1; &()*+,-./:;<=>?@[]^_{|}~", "1" ; "Test #103: 1; &()*+,-./:;<=>?@[]^_{|}~ => 1")]
    fn step_1_tester(input: &str, output: &str) {
        let expr = *reader::read_str(input).expect("Malformed input");
        assert_eq!(printer::pr_str(eval(AST { expr })), output)
    }
}
