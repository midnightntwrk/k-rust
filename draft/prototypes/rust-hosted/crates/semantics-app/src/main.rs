use krs::{Definition, Term, constructor, rule};
use semantics_lib::Expr;

#[constructor(sort = Expr, syntax = "app")]
pub struct App;

#[rule]
pub fn app_step(App: Term<dyn Expr>) -> Term<dyn Expr> {
    App
}

fn main() {
    // Force the dependency into the linked definition even though authored
    // declarations are otherwise consumed through distributed registration.
    let _ = std::any::TypeId::of::<semantics_lib::Foo>();

    let definition = Definition::collect().analyze().expect("valid definition");
    assert!(definition.is_subsort("Value", "Expr"));
    assert!(definition.is_subsort("Value", "KResult"));
    assert!(definition.is_subsort("Value", "KItem"));

    let kore = krs::native::compile_smoke(&definition).expect("native k-rust handoff");
    assert!(kore.contains("foo"));
    assert!(kore.contains("bar"));

    for path in definition.stable_paths() {
        println!("{path}");
    }
    println!("structured descriptors -> k-rust -> KORE passed");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collection_is_sorted_and_crosses_crate_and_module_boundaries() {
        let definition = Definition::collect().analyze().unwrap();
        let paths = definition.stable_paths();
        assert!(paths.windows(2).all(|pair| pair[0] <= pair[1]));
        assert!(paths.iter().any(|path| path.contains("semantics-lib")));
        assert!(paths.iter().any(|path| path.contains("semantics_app")));
        assert!(paths.iter().any(|path| path.contains("nested")));
    }

    #[test]
    fn diamond_closure_is_path_independent() {
        let definition = Definition::collect().analyze().unwrap();
        let value_id = &definition.sort_ids_by_name["Value"][0];
        let ancestors = &definition.subsort_closure[value_id];
        assert_eq!(ancestors.len(), 4);
        assert!(definition.is_subsort("Value", "Expr"));
        assert!(definition.is_subsort("Value", "KResult"));
        assert!(definition.is_subsort("Value", "KItem"));
    }
}

