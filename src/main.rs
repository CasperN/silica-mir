mod ast;
mod parser;
mod tc;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <file.silica>", args[0]);
        std::process::exit(1);
    }

    let path = &args[1];
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Failed to read file '{}': {}", path, e);
            std::process::exit(1);
        }
    };

    let p = parser::Parser::new(source);
    let program = match p.parse() {
        Ok(program) => program,
        Err(err) => {
            eprintln!("Parse error: {}", err);
            std::process::exit(1);
        }
    };

    println!("AST parsed successfully.");

    let env = match tc::Env::build(&program) {
        Ok(env) => env,
        Err(err) => {
            eprintln!("Environment build error: {}", err);
            std::process::exit(1);
        }
    };

    match env.typecheck() {
        Ok(()) => {
            println!("Type checking successful!");
        }
        Err(err) => {
            eprintln!("Type checking error: {}", err);
            std::process::exit(1);
        }
    }
}
