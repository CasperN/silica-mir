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
        let program = Parser::parse_or_panic(src);
        let mut d = Diagnostics::default();
        let env = type_check::GlobalEnv::build(&program).0;
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
        let program = Parser::parse_or_panic(src);
        let mut d = Diagnostics::default();
        let env = type_check::GlobalEnv::build(&program).0;
        check_return_leaks(&program, &env, &mut d);
        let errs = d.errors_str();
        let leak_errs: Vec<_> = errs
            .iter()
            .filter(|e| e.contains("not consumed at return"))
            .collect();
        assert!(leak_errs.is_empty(), "expected no leaks, got {:?}", errs);
    }
}

mod nested_reference_state_tests {
    use super::super::check::check_program;
    use crate::diagnostics::Diagnostics;
    use crate::mir::parser::Parser;
    use crate::mir::env::GlobalEnv;

    fn errors(source: &str) -> Vec<String> {
        let program = Parser::parse_or_panic(source);
        let env = GlobalEnv::build(&program).0;
        let mut diagnostics = Diagnostics::default();
        check_program(&program, &env, &mut diagnostics);
        diagnostics.errors_str()
    }

    #[test]
    fn tracks_move_and_restore_through_multiple_exclusive_dereferences() {
        let errs = errors(
            "
            extern fn consume(x: i64);
            fn f(r: &mut &mut &mut i64) {
              entry:
                call consume(move r.*.*.*);
                r.*.*.* = 0;
                return
            }
            ",
        );
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
    }

    #[test]
    fn reports_unrestored_nested_exclusive_pointee() {
        let errs = errors(
            "
            extern fn consume(x: i64);
            fn f(r: &mut &mut i64) {
              entry:
                call consume(move r.*.*);
                return
            }
            ",
        );
        assert!(
            errs.iter().any(|error| {
                error.contains("reference 'r.*' has unfulfilled obligation")
                    && error.contains("pointee is uninitialized")
            }),
            "expected nested obligation error, got {errs:?}"
        );
    }

    #[test]
    fn rejects_move_through_a_shared_boundary_at_any_depth() {
        let errs = errors(
            "
            extern fn consume(x: i64);
            fn f(r: &&mut i64) {
              entry:
                call consume(move r.*.*);
                return
            }
            ",
        );
        assert!(
            errs.iter()
                .any(|error| error.contains("cannot move out through shared reference 'r'")),
            "expected shared-boundary error, got {errs:?}"
        );
    }

    #[test]
    fn transfers_a_nested_reference_out_and_back_with_its_state() {
        let errs = errors(
            "
            extern fn consume(x: i64);
            fn f(r: &mut &mut i64) {
              s: &mut i64;
              entry:
                s = move r.*;
                call consume(move s.*);
                s.* = 0;
                r.* = move s;
                return
            }
            ",
        );
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
    }

    #[test]
    fn transferred_nested_reference_keeps_an_unfulfilled_obligation() {
        let errs = errors(
            "
            extern fn consume(x: i64);
            fn f(r: &mut &mut i64) {
              s: &mut i64;
              entry:
                s = move r.*;
                call consume(move s.*);
                r.* = move s;
                return
            }
            ",
        );
        assert!(
            errs.iter().any(|error| {
                error.contains("reference 'r.*' has unfulfilled obligation")
                    && error.contains("pointee is uninitialized")
            }),
            "expected transferred nested obligation error, got {errs:?}"
        );
    }

    #[test]
    fn joins_nested_pointee_state_across_control_flow() {
        let errs = errors(
            "
            extern fn consume(x: i64);
            fn f(r: &mut &mut i64, take: bool) {
              x: i64;
              entry:
                branch(copy take) [true: moved, false: kept]
              moved:
                call consume(move r.*.*);
                goto join
              kept:
                goto join
              join:
                x = copy r.*.*;
                drop x;
                return
            }
            ",
        );
        assert!(
            errs.iter().any(|error| {
                error.contains("cannot read from pointee of 'r.*'")
                    && error.contains("inconsistent state")
            }),
            "expected divergent nested pointee error, got {errs:?}"
        );
    }

    #[test]
    fn both_branches_materialize_nested_pointee_and_agree() {
        // Independent materialization of the same nested ref-state key on
        // both arms must survive the join. Both branches read the same
        // deep pointee without consuming it, so the join sees the declared
        // (Init, Init) obligation on both sides and a subsequent read
        // succeeds.
        let errs = errors(
            "
            extern fn consume(x: i64);
            fn f(r: &mut &mut i64, take: bool) {
              x: i64;
              y: i64;
              entry:
                branch(copy take) [true: left, false: right]
              left:
                x = copy r.*.*;
                call consume(move x);
                goto join
              right:
                x = copy r.*.*;
                call consume(move x);
                goto join
              join:
                y = copy r.*.*;
                call consume(move y);
                drop take;
                return
            }
            ",
        );
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
    }
}
