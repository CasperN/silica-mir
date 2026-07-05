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

    let (env, mut errors) = tc::Env::build(&program);
    errors.extend(env.typecheck());
    let mut warnings: Vec<String> = Vec::new();

    let ev = enum_variants::check_program(&env);
    errors.extend(ev.errors);
    warnings.extend(ev.warnings);

    let br = block_reachability::check_program(&env);
    errors.extend(br.errors);
    warnings.extend(br.warnings);

    for w in &warnings {
        eprintln!("Warning: {}", w);
    }

    if !errors.is_empty() {
        for e in &errors {
            eprintln!("Error: {}", e);
        }
        eprintln!("{} error(s), {} warning(s)", errors.len(), warnings.len());
        std::process::exit(1);
    }

    println!("Type checking successful!");
    if !warnings.is_empty() {
        println!("({} warning(s))", warnings.len());
    }
}
