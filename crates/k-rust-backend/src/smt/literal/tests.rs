//! The reader's bounded admission and actual emitted value checked against the native hook.

use super::*;
use crate::term::{FunctionType, SymbolAttributes, SymbolType, Variable};
use std::sync::Arc;

fn symbol(hook: &str, sort: Sort) -> Symbol {
    let mut attributes = SymbolAttributes::constructor().with_declared_function(true);
    attributes.hook = Some(hook.into());
    attributes.symbol_type = SymbolType::Function(FunctionType::Total);
    Symbol {
        name: "test-bit-operation".into(),
        sort_variables: Vec::new(),
        argument_sorts: vec![sort; 2],
        result_sort: sort,
        attributes,
    }
}

fn int(value: impl ToString) -> Term {
    Term::raw_domain_value(Sort::simple("SortInt"), value.to_string())
}

#[test]
fn admission_bounds_masks_amounts_and_builtin_sorts() {
    let sort = Sort::simple("SortInt");
    let x = Term::variable(Variable::new("X", sort));
    let and = symbol("INT.and", sort);
    for mask in [
        BigInt::from(-1),
        BigInt::from(1u8) << AMOUNT_LIMIT,
        (0..=RUN_LIMIT).fold(BigInt::from(0), |m, i| m | (BigInt::from(1u8) << (2 * i))),
    ] {
        assert!(read(&and, &sort, &[x.clone(), int(mask)]).is_none());
    }
    for offset in [-1, i64::from(AMOUNT_LIMIT) + 1] {
        assert!(read(&symbol("INT.shl", sort), &sort, &[x.clone(), int(offset)]).is_none());
    }
    let custom = Sort::simple("RenamedInt");
    let renamed = Term::raw_domain_value(custom, "1");
    assert!(
        read(
            &symbol("INT.and", custom),
            &custom,
            &[renamed.clone(), renamed]
        )
        .is_none()
    );
    assert!(read(&and, &custom, &[x.clone(), int(1)]).is_none());
    assert!(read(&and, &sort, &[int(1), Term::raw_domain_value(custom, "1")]).is_none());
}

#[test]
fn a_sparse_mask_shares_its_composite_operand_in_definition_free_translation() {
    let sort = Sort::simple("SortInt");
    let x = Term::variable(Variable::new("X", sort));
    let shift = Term::application(
        Arc::new(symbol("INT.shl", sort)),
        Vec::new(),
        vec![x, int(1)],
    );
    for hook in ["INT.and", "INT.or", "INT.xor"] {
        let term = Term::application(
            Arc::new(symbol(hook, sort)),
            Vec::new(),
            vec![shift.clone(), int(165)],
        );
        let mut state = TranslationState::new();
        let text = state.translate_term(&term).unwrap().to_string();
        assert_eq!(text.matches("(* SMT-1 2)").count(), 1, "{text}");
        assert!(text.starts_with("(let "), "{text}");
        assert_eq!(state.exactness(), super::super::Exactness::Exact);
    }
}

#[cfg(feature = "z3")]
#[test]
fn emitted_integer_readings_agree_with_native_signed_hook_values() {
    let sort = Sort::simple("SortInt");
    let mut checks = Vec::new();
    for hook in ["INT.and", "INT.or", "INT.xor", "INT.shl"] {
        for x in [-65537, -257, -1, 0, 127, 255, 256, 65536] {
            let amounts: &[i64] = if hook == "INT.shl" {
                &[0, 1, 8, 16]
            } else {
                &[0, 6, 128, 165, 255, 61680]
            };
            for amount in amounts {
                let arguments = [int(x), int(amount)];
                let value = match crate::builtin::evaluate_hook(hook, &arguments)
                    .unwrap()
                    .unwrap()
                {
                    crate::builtin::BuiltinResult::Value(value) => read_int(&value).unwrap(),
                    other @ (crate::builtin::BuiltinResult::NotApplicable
                    | crate::builtin::BuiltinResult::Bottom
                    | crate::builtin::BuiltinResult::Effect(_)
                    | crate::builtin::BuiltinResult::Unsupported(_)) => {
                        panic!("{hook} {x} {amount}: {other:?}")
                    }
                };
                let translated = read(&symbol(hook, sort), &sort, &arguments)
                    .unwrap()
                    .translate(&mut TranslationState::new())
                    .unwrap();
                checks.push(format!("(distinct {translated} {value})"));
            }
        }
    }
    let solver = z3::Solver::new();
    solver.from_string(format!("(assert (or {}))", checks.join(" ")));
    assert_eq!(solver.check(), z3::SatResult::Unsat);
}
