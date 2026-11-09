//! The linked Z3 decides queries over prime fields, through its C API and through the SMT-LIB
//! scripts the backend sends.
//!
//! Z3 5.x has a theory of finite fields of prime order: a sort `(_ FiniteField p)`, the operators
//! `ff.add`, `ff.mul`, `ff.neg` and `ff.bitsum`, and numerals `(as ffN (_ FiniteField p))`. The
//! `z3` crate has no type for it, so the C API is reached through `z3-sys` on the crate's context,
//! and the backend's script route reads it as written. The backend emits no such query: these
//! tests show that the theory is there for a definition that will.
//!
//! The query: in the field of 7 elements, `x * x = 2` has the solutions 3 and 4 (`9 = 2` and
//! `16 = 2` modulo 7), and `x * x = 3` has none, since the squares modulo 7 are 0, 1, 2 and 4.

use std::ffi::{CStr, CString};

use z3::ast::{Ast, Bool, Dynamic};

use super::*;
use crate::smt::z3::tests::{answers, definition};

/// The field of 7 elements made through the C API, with `x` and `x * x` over it.
struct Field {
    x: Dynamic,
    square: Dynamic,
    context: z3::Context,
    sort: z3_sys::Z3_sort,
}

impl Field {
    fn new() -> Self {
        let context = z3::Context::thread_local();
        let c = context.get_z3_context();
        let prime = CString::new("7").unwrap();
        // SAFETY: `c` is the live context `context` holds, and `prime` a NUL-terminated string
        // that outlives the call. The sort is kept alive by a reference of its own, which the
        // field drops.
        let sort = unsafe { z3_sys::Z3_mk_finite_field_sort(c, prime.as_ptr()) }
            .expect("Z3 makes the field of 7 elements");
        // SAFETY: as above; a sort is an AST of the context.
        unsafe { z3_sys::Z3_inc_ref(c, z3_sys::Z3_sort_to_ast(c, sort).unwrap()) };
        let name = CString::new("x").unwrap();
        // SAFETY: as above; `Dynamic::wrap` takes a reference of its own to the constant.
        let x = unsafe {
            let symbol = z3_sys::Z3_mk_string_symbol(c, name.as_ptr()).unwrap();
            Dynamic::wrap(&context, z3_sys::Z3_mk_const(c, symbol, sort).unwrap())
        };
        let factors = [x.get_z3_ast(), x.get_z3_ast()];
        // SAFETY: as above; the factors are live ASTs of the context, of the field's sort.
        let square = unsafe {
            Dynamic::wrap(
                &context,
                z3_sys::Z3_mk_ff_mul(c, 2, factors.as_ptr()).expect("x * x in the field"),
            )
        };
        Self {
            x,
            square,
            context,
            sort,
        }
    }

    /// The element `value` of the field.
    fn numeral(&self, value: u32) -> Dynamic {
        let c = self.context.get_z3_context();
        let text = CString::new(value.to_string()).unwrap();
        // SAFETY: as in `new`.
        unsafe {
            Dynamic::wrap(
                &self.context,
                z3_sys::Z3_mk_numeral(c, text.as_ptr(), self.sort).expect("a numeral of the field"),
            )
        }
    }

    /// The order of the field as Z3 reports it.
    fn size(&self) -> String {
        let c = self.context.get_z3_context();
        // SAFETY: the sort is live (the field holds a reference), and the returned string is
        // copied before any other API call.
        unsafe { CStr::from_ptr(z3_sys::Z3_get_finite_field_sort_size(c, self.sort)) }
            .to_string_lossy()
            .into_owned()
    }

    fn kind(&self) -> z3_sys::SortKind {
        // SAFETY: as in `size`.
        unsafe { z3_sys::Z3_get_sort_kind(self.context.get_z3_context(), self.sort) }
    }

    /// `x * x = value`.
    fn square_is(&self, value: u32) -> Bool {
        self.square.eq(self.numeral(value))
    }
}

impl Drop for Field {
    fn drop(&mut self) {
        let c = self.context.get_z3_context();
        // SAFETY: the reference `new` took.
        unsafe { z3_sys::Z3_dec_ref(c, z3_sys::Z3_sort_to_ast(c, self.sort).unwrap()) };
    }
}

/// A finite-field sort made through the C API is a field of the given order, and a solver over it
/// finds a square root where one exists, and refutes one where none does.
#[test]
fn the_c_api_makes_a_prime_field_and_decides_a_query_over_it() {
    on_own_context(|| {
        let field = Field::new();
        assert_eq!(field.size(), "7");
        assert_eq!(field.kind(), z3_sys::SortKind::FiniteField);

        let solver = Solver::new();
        let has_root = field.square_is(2);
        solver.assert(&has_root);
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().expect("a model of a satisfiable check");
        let root = model.eval(&field.x, true).expect("x's value");
        assert!(
            [3, 4]
                .into_iter()
                .any(|value| model.eval(&root.eq(field.numeral(value)), true)
                    == Some(Bool::from_bool(true))),
            "x = {root}"
        );

        let solver = Solver::new();
        solver.assert(field.square_is(3));
        assert_eq!(solver.check(), SatResult::Unsat);
    });
}

/// The backend's own script route reads the theory's SMT-LIB syntax and decides the same queries
/// under its resource-bounded options, as it decides any script.
#[test]
fn the_backends_script_route_decides_a_prime_field_query() {
    let script = |value: u32| {
        format!(
            "(define-sort F () (_ FiniteField 7))\n(declare-const x F)\n\
             (assert (= (ff.mul x x) (as ff{value} F)))"
        )
    };
    let solver = Z3Solver::with_options(
        &definition(),
        Z3Options {
            budget: SmtBudget::Units(std::num::NonZeroU32::new(1_000_000).unwrap()),
            retry_limit: 3,
        },
    )
    .unwrap();
    assert_eq!(answers(&solver, &script(2), 1), "S");
    assert_eq!(answers(&solver, &script(3), 1), "U");
}
