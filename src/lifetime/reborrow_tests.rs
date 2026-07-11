//! Reborrow tests — `s = &kind *r`.
//!
//! Covers: loan tracking on `*r` (accesses to r and *r conflict with
//! the reborrow loan), init-state precondition (kind's cur must match
//! r's pointee is_init), init-state eager transition (r resumes at
//! kind's post when s expires), NLL insertion ordering (children
//! before parents), and chained reborrows.

use crate::test_util::*;

// ---------- Basic reborrow loan tracking ----------

#[test]
fn mut_reborrow_of_mut_ok() {
    // r loans x, s reborrows r. NLL inserts unborrow s (via call),
    // then unborrow r; r's obligation is fulfilled (cur=Init from
    // eager transition of &mut, ends=Init).
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut number);
        fn f(x: number) {
          r: &mut number;
          s: &mut number;
          entry:
            r = &mut x;
            s = &mut *r;
            call sink(move s);
            return
        }
        ",
    );
}

#[test]
fn access_r_while_reborrow_live_conflicts() {
    // r is suspended by s. `copy *r` between the reborrow and s's
    // consumption reads through r while s's loan is active — errors.
    let (errs, _) = run("
        extern fn sink(r: &mut number);
        fn f(x: number) {
          r: &mut number;
          s: &mut number;
          y: number;
          entry:
            r = &mut x;
            s = &mut *r;
            y = copy *r;
            call sink(move s);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot read '*r': already borrowed by 's'"]);
}

#[test]
fn access_x_while_reborrow_live_conflicts() {
    // r's loan on x is still active during s's lifetime, so direct
    // access to x still fails through the r-loan (unchanged behavior;
    // reborrow doesn't remove the parent's loan).
    let (errs, _) = run("
        extern fn sink(r: &mut number);
        fn f(x: number) {
          r: &mut number;
          s: &mut number;
          entry:
            r = &mut x;
            s = &mut *r;
            x = 1;
            call sink(move s);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'x': already borrowed by 'r'"]);
}

// ---------- Kind precondition ----------

#[test]
fn mut_reborrow_of_out_precondition_fails() {
    // r: &out number → r.is_init = false at param entry. &mut *r
    // requires the pointee to be initialized. Rejected.
    let (errs, _) = run("
        extern fn sink(r: &mut number);
        fn f(r: &out number) {
          s: &mut number;
          entry:
            s = &mut *r;
            call sink(move s);
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot create &mut of '*r': pointee must be initialized at borrow, but is uninitialized"],
    );
}

#[test]
fn out_reborrow_of_out_ok_when_pointee_written() {
    // r: &out number, s: &out *r fulfilling r's obligation transitively.
    // After s's *s = 42, r.is_init becomes true (via eager on &out).
    // r resumes and its own &out obligation is met.
    assert_no_diagnostics(
        "
        fn f(r: &out number) {
          s: &out number;
          entry:
            s = &out *r;
            *s = 42;
            return
        }
        ",
    );
}

#[test]
fn out_reborrow_of_mut_precondition_fails() {
    // r: &mut number → pointee Init. &out *r requires Uninit. Rejected.
    let (errs, _) = run("
        extern fn sink(r: &out number);
        fn f(r: &mut number) {
          s: &out number;
          entry:
            s = &out *r;
            *s = 1;
            call sink(move s);
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot create &out of '*r': pointee must be uninitialized at borrow, but is initialized"],
    );
}

// ---------- Shared reborrow ----------

#[test]
fn shared_reborrow_of_mut_ok() {
    // & *r on r: &mut — shared reborrow permitted; s is Copy Drop, so
    // NLL closes it and r resumes. No obligation on s.
    assert_no_diagnostics(
        "
        extern fn read_ref(r: &number);
        fn f(x: number) {
          r: &mut number;
          s: &number;
          entry:
            r = &mut x;
            s = &*r;
            call read_ref(move s);
            return
        }
        ",
    );
}

// ---------- Chained reborrow ----------

#[test]
fn chained_reborrow_t_from_s_from_r_ok() {
    // Three-level reborrow: r loans x, s reborrows r, t reborrows s.
    // NLL should unborrow in child-first order: t (via natural
    // consume by call), then s, then r.
    assert_no_diagnostics(
        "
        extern fn sink(t: &mut number);
        fn f(x: number) {
          r: &mut number;
          s: &mut number;
          t: &mut number;
          entry:
            r = &mut x;
            s = &mut *r;
            t = &mut *s;
            call sink(move t);
            return
        }
        ",
    );
}

// ---------- Reference param reborrow ----------

#[test]
fn reborrow_of_mut_param_ok() {
    // A ref param r: &mut number, reborrowed into local s. s's use
    // via *s reads through r; s expires; r resumes; r's own
    // obligation ends the function.
    assert_no_diagnostics(
        "
        extern fn read_ref(r: &number);
        fn f(r: &mut number) {
          s: &number;
          entry:
            s = &*r;
            call read_ref(move s);
            return
        }
        ",
    );
}

// ---------- NLL insertion order (child before parent) ----------

#[test]
fn nll_inserts_child_unborrow_before_parent() {
    // s reborrows r; s dies at the same point as r. NLL must emit
    // unborrow s BEFORE unborrow r, else unborrow r would conflict
    // with s's loan. Full-pipeline clean run implies the order is
    // correct (checker rejects the wrong order).
    assert_no_diagnostics(
        "
        fn f(r: &out number) {
          s: &out number;
          entry:
            s = &out *r;
            *s = 42;
            return
        }
        ",
    );
}

// ---------- Reborrow across loop iterations ----------

#[test]
fn reborrow_in_loop_body_ok() {
    // Reborrow `s = &mut *r` inside a loop body. Each iteration
    // creates a fresh s, uses it, drops it (via call). r stays live
    // across the back-edge and NLL closes it on the loop-exit edge.
    assert_no_diagnostics(
        "
        extern fn use_mut(r: &mut number);
        fn f(x: number, b: boolean) {
          r: &mut number;
          s: &mut number;
          entry:
            r = &mut x;
            goto head
          head:
            branch(copy b) [true: body, false: done]
          body:
            s = &mut *r;
            call use_mut(move s);
            goto head
          done:
            return
        }
        ",
    );
}
