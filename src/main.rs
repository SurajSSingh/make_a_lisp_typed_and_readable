use rprompt::prompt_reply;

fn read(line: String) -> String {
    todo!()
}

fn eval(ast: String) -> String {
    todo!()
}

fn print(value: String) {
    println!("{value}")
}

fn rep(input: String) {
    print(input)
}

fn main() {
    loop {
        let Ok(input) = prompt_reply("user>") else {
            break;
        };
        rep(input);
    }
}
