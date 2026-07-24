mod direct_leak_check_tests {
    //! Pass-level tests that invoke `check_return_leaks` directly on a
    //! non-elaborated program. Kept as unit tests because the fixture
    //! runner exercises the full pipeline (post-drop-elab), which would
    //! insert `drop x` and hide the pre-elaboration leak these tests
    //! deliberately observe.

    use super::super::check::check_return_leaks;
    use crate::diagnostics::Diagnostics;
    use crate::mir::parser::Parser;
    use crate::mir::type_check;

    #[test]
    fn flags_pre_elaboration_drop_leak() {
        let src = "fn f(x: i64) { entry: return }";
        let program = Parser::new(src.to_string()).parse().unwrap();
        let mut d = Diagnostics::default();
        let env = type_check::Env::build(&program).0;
        check_return_leaks(&program, &env, &mut d);
        let errs = d.errors_str();
        assert!(
            errs.iter()
                .any(|e| e.contains("value 'x'") && e.contains("not consumed")),
            "expected leak error, got {:?}",
            errs
        );
    }

    #[test]
    fn ok_when_explicitly_dropped() {
        let src = "fn f(x: i64) { entry: drop x; return }";
        let program = Parser::new(src.to_string()).parse().unwrap();
        let mut d = Diagnostics::default();
        let env = type_check::Env::build(&program).0;
        check_return_leaks(&program, &env, &mut d);
        let errs = d.errors_str();
        let leak_errs: Vec<_> = errs
            .iter()
            .filter(|e| e.contains("not consumed at return"))
            .collect();
        assert!(leak_errs.is_empty(), "expected no leaks, got {:?}", errs);
    }
}
