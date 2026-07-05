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

    let (env, mut errors) = tc::Env::build(&program);
    errors.extend(env.typecheck());

    if errors.is_empty() {
        println!("Type checking successful!");
    } else {
        for e in &errors {
            eprintln!("Error: {}", e);
        }
        eprintln!("{} error(s)", errors.len());
        std::process::exit(1);
    }
}
