mod parameter_ref_tests {
    use crate::mir::env::IndexedProgram;
    use crate::mir::helpers::*;
    use crate::mir::parser::Parser;
    use crate::mir::place_state::analysis::{boundary_state, InitState, RefState};

    #[test]
    fn seeds_nested_struct_parameter_reference_obligations() {
        let program = Parser::parse_or_panic(
            "
            struct Inner: Move { r: &out i64 }
            struct Outer: Move { inner: Inner }
            fn f(p: Outer) { entry: return }
            ",
        );
        let env = IndexedProgram::build(&program).0;
        let func = program.find_fn("f").expect("fn f");
        let body = func.body.as_ref().expect("body");

        let state = boundary_state(func, body, &env);
        let field = field_place(field_place(var_place("p"), "inner"), "r");
        assert_eq!(
            state.refs.get(&field),
            Some(&RefState {
                pointee: InitState::NeverInit,
                ends_init: true,
            })
        );
    }

    #[test]
    fn invalid_copy_does_not_clone_reference_obligations_in_dataflow() {
        let program = Parser::parse_or_panic(
            "
            struct Linear: Move { r: &out i64 }
            fn f(x: Linear) {
              y: Linear;
              entry:
                y = copy x;
                return
            }
            ",
        );
        let env = IndexedProgram::build(&program).0;
        let func = program.find_fn("f").expect("fn f");
        let states = super::super::analysis::states_before_returns(&env, func);
        let state = &states[0].1;
        assert!(state.refs.contains_key(&field_place(var_place("x"), "r")));
        assert!(!state.refs.contains_key(&field_place(var_place("y"), "r")));
    }
}
