//! Type-level predicates and helpers shared across passes.
//!
//! Cross-cutting queries about MIR `Type`s that don't belong to any
//! single pass: inhabitedness, in the future substitution / occurs-
//! check for generics, etc.

use crate::mir::ast::Type;
use crate::mir::type_check::{Env, TypeDecl};
use std::collections::BTreeSet;

/// True if a value of `ty` cannot be constructed. Uninhabited types:
/// - `never` — the axiom.
/// - Struct where any field is uninhabited (whole-value construction
///   requires every field).
/// - Enum where every variant's payload is uninhabited (no variant
///   is constructible → the enum is empty).
/// - Non-empty array of an uninhabited element type. `[T; 0]` is
///   inhabited (the empty array literal has no elements to construct).
///
/// References, raw pointers, function pointers, scalars, `unit`, and
/// `bool` are always inhabited. Recursive struct/enum types are
/// bounded by the visited set — a Custom name seen twice in the
/// same walk conservatively returns false (inhabited) rather than
/// looping.
pub fn is_type_uninhabited(ty: &Type, env: &Env) -> bool {
    fn walk(ty: &Type, env: &Env, visited: &mut BTreeSet<String>) -> bool {
        match ty {
            Type::Never => true,
            Type::Custom(name, _) => {
                if !visited.insert(name.clone()) {
                    return false;
                }
                let out = match env.types.get(name) {
                    Some(TypeDecl::Struct(s)) => {
                        s.fields.iter().any(|f| walk(&f.ty, env, visited))
                    }
                    // An enum is uninhabited when EVERY variant is
                    // uninhabited. Vacuous truth handles the empty
                    // enum (no variants → all() returns true).
                    Some(TypeDecl::Enum(e)) => {
                        e.variants.iter().all(|v| walk(&v.ty, env, visited))
                    }
                    None => false,
                };
                visited.remove(name);
                out
            }
            Type::Array(elem, n) => *n > 0 && walk(elem, env, &mut BTreeSet::new()),
            _ => false,
        }
    }
    walk(ty, env, &mut BTreeSet::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::ast::Program;
    use crate::mir::helpers::*;
    use crate::mir::parser::Parser;

    /// Build an Env from MIR source, discarding any diagnostics.
    fn env_of(src: &str) -> Env {
        let program: Program = Parser::new(src.to_string()).parse().unwrap();
        Env::build(&program).0
    }

    #[test]
    fn never_is_uninhabited() {
        let env = env_of("fn f() { entry: return }");
        assert!(is_type_uninhabited(&never_ty(), &env));
    }

    #[test]
    fn scalars_are_inhabited() {
        let env = env_of("fn f() { entry: return }");
        assert!(!is_type_uninhabited(&i64_ty(), &env));
        assert!(!is_type_uninhabited(&bool_ty(), &env));
        assert!(!is_type_uninhabited(&unit_ty(), &env));
    }

    #[test]
    fn struct_with_never_field_is_uninhabited() {
        let env = env_of("struct S { a: i64 b: never } fn f() { entry: return }");
        assert!(is_type_uninhabited(&custom_ty("S"), &env));
    }

    #[test]
    fn struct_with_all_inhabited_fields_is_inhabited() {
        let env = env_of("struct S { a: i64 b: bool } fn f() { entry: return }");
        assert!(!is_type_uninhabited(&custom_ty("S"), &env));
    }

    #[test]
    fn empty_enum_is_uninhabited() {
        // No variants → vacuous truth: every variant is uninhabited.
        let env = env_of("enum E { } fn f() { entry: return }");
        assert!(is_type_uninhabited(&custom_ty("E"), &env));
    }

    #[test]
    fn enum_with_one_inhabited_variant_is_inhabited() {
        let env = env_of("enum E { A: i64 B: never } fn f() { entry: return }");
        assert!(!is_type_uninhabited(&custom_ty("E"), &env));
    }

    #[test]
    fn enum_with_all_never_variants_is_uninhabited() {
        let env = env_of("enum E { A: never B: never } fn f() { entry: return }");
        assert!(is_type_uninhabited(&custom_ty("E"), &env));
    }

    #[test]
    fn zero_length_array_of_never_is_inhabited() {
        // `[Never; 0]` has no elements to construct — trivially inhabited
        // by the empty array literal.
        let env = env_of("fn f() { entry: return }");
        let ty = Type::Array(Box::new(Type::Never), 0);
        assert!(!is_type_uninhabited(&ty, &env));
    }

    #[test]
    fn nonempty_array_of_never_is_uninhabited() {
        let env = env_of("fn f() { entry: return }");
        let ty = Type::Array(Box::new(Type::Never), 3);
        assert!(is_type_uninhabited(&ty, &env));
    }

    #[test]
    fn recursive_via_reference_does_not_loop() {
        // A recursive-through-reference struct: the walker must not
        // infinitely recurse into `S`'s own name; the visited set
        // conservatively treats a second occurrence as inhabited.
        let env = env_of("struct S { r: &S } fn f() { entry: return }");
        assert!(!is_type_uninhabited(&Type::Custom("S".into(), Vec::new()), &env));
    }

    #[test]
    fn references_are_always_inhabited() {
        // Even a reference to Never is a fine reference value.
        let env = env_of("fn f() { entry: return }");
        let ty = Type::Ref(crate::mir::ast::RefKind::Shared, Box::new(Type::Never));
        assert!(!is_type_uninhabited(&ty, &env));
    }
}

