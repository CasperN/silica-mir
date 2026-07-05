mod ast;
mod block_reachability;
mod diagnostics;
mod enum_variants;
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

    let mut d = diagnostics::Diagnostics::default();
    let env = tc::Env::build(&program, &mut d);
    env.typecheck(&mut d);
    enum_variants::check_program(&env, &mut d);
    block_reachability::check_program(&env, &mut d);

    for w in &d.warnings {
        eprintln!("Warning: {}", w);
    }

    if !d.errors.is_empty() {
        for e in &d.errors {
            eprintln!("Error: {}", e);
        }
        eprintln!("{} error(s), {} warning(s)", d.errors.len(), d.warnings.len());
        std::process::exit(1);
    }

    println!("Type checking successful!");
    if !d.warnings.is_empty() {
        println!("({} warning(s))", d.warnings.len());
    }
}
