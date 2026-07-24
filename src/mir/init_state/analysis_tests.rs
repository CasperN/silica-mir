mod parameter_ref_tests {
    use crate::mir::ast::*;
    use crate::mir::helpers::*;
    use crate::mir::init_state::analysis::{InitState, RefState, initial_state};
    use crate::mir::parser::Parser;
    use crate::mir::type_check::Env;

    #[test]
    fn seeds_nested_struct_parameter_reference_obligations() {
        let program = Parser::new(
            "
            struct Inner: Move { r: &out i64 }
            struct Outer: Move { inner: Inner }
            fn f(p: Outer) { entry: return }
            ",
        )
        .parse()
        .expect("parse");
        let env = Env::build(&program).0;
        let func = program.find_fn("f").expect("fn f");
        let body = func.body.as_ref().expect("body");

        let state = initial_state(func, body, &env);
        let field = field_place(field_place(var_place("p"), "inner"), "r");
        assert_eq!(
            state.refs.get(&field),
            Some(&RefState {
                pointee: InitState::NeverInit,
                ends_init: true,
            })
        );
    }
}
