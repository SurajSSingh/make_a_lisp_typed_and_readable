use rustyline::{error::ReadlineError, DefaultEditor, Result};

fn read(rl: &mut DefaultEditor) -> Result<String> {
    let line = rl.readline("user> ")?;
    rl.add_history_entry(line.clone())?;
    Ok(line)
}

fn eval(ast: &str) -> &str {
    ast
}

fn print(value: &str) {
    println!("{value}")
}

fn rep(rl: &mut DefaultEditor) -> Result<()> {
    print(eval(&read(rl)?));
    Ok(())
}

pub fn main() -> Result<()> {
    let mut rl = DefaultEditor::new()?;

    loop {
        if let Err(err) = rep(&mut rl) {
            match err {
                ReadlineError::Eof | ReadlineError::Interrupted => break,
                _ => {
                    println!("{}", err);
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

    #[test_case("abcABC123", "abcABC123" ; "Testing basic string")]
    #[test_case("hello mal world", "hello mal world" ; "Testing string containing spaces")]
    #[test_case("[]{}\"'* ;:()", "[]{}\"'* ;:()" ; "Testing string containing symbols")]
    #[test_case("hello world abcdefghijklmnopqrstuvwxyz ABCDEFGHIJKLMNOPQRSTUVWXYZ 0123456789 (;:() []{}\"'* ;:() []{}\"'* ;:() []{}\"'*)", "hello world abcdefghijklmnopqrstuvwxyz ABCDEFGHIJKLMNOPQRSTUVWXYZ 0123456789 (;:() []{}\"'* ;:() []{}\"'* ;:() []{}\"'*)" ; "Test long string")]
    #[test_case("!", "!" ; "Test #1: ! => !")]
    #[test_case("&", "&" ; "Test #2: & => &")]
    #[test_case("+", "+" ; "Test #3: + => +")]
    #[test_case(",", "," ; "Test #4: , => ,")]
    #[test_case("-", "-" ; "Test #5: - => -")]
    #[test_case("/", "/" ; "Test #6: / => /")]
    #[test_case("<", "<" ; "Test #7: < => <")]
    #[test_case("=", "=" ; "Test #8: = => =")]
    #[test_case(">", ">" ; "Test #9: > => >")]
    #[test_case("?", "?" ; "Test #10: ? => ?")]
    #[test_case("@", "@" ; "Test #11: @ => @")]
    #[test_case("^", "^" ; "Test #12: ^ => ^")]
    #[test_case("_", "_" ; "Test #13: _ => _")]
    #[test_case("`", "`" ; "Test #14: ` => `")]
    #[test_case("~", "~" ; "Test #15: ~ => ~")]
    #[test_case("#", "#" ; "Test #16: # => #")]
    #[test_case("$", "$" ; "Test #17: $ => $")]
    #[test_case("%", "%" ; "Test #18: % => %")]
    #[test_case(".", "." ; "Test #19: . => .")]
    #[test_case("|", "|" ; "Test #20: | => |")]
    fn step_0_tester(input: &str, output: &str) {
        assert_eq!(eval(input), output)
    }
}
