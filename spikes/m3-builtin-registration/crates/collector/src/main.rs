use std::collections::BTreeMap;

use dialect::{BuiltinSort, HostBuiltinRegistration};

fn sort_name(sort: BuiltinSort) -> &'static str {
    match sort {
        BuiltinSort::Int => "Int",
    }
}

fn main() {
    // An explicit dependency reference models the generated KRS collector's
    // intentional retention of selected semantics crates.
    let calls = m3_builtin_semantics::application_calls();
    let mut builtins = BTreeMap::new();
    for registration in dialect::builtin_registrations() {
        assert!(
            builtins
                .insert((registration.type_key)(), registration)
                .is_none(),
            "duplicate builtin marker type"
        );
    }
    assert_eq!(builtins.len(), 2);
    let add = builtins
        .values()
        .find(|entry| entry.operation == dialect::BuiltinOp::IntAdd)
        .expect("add registration");
    let sub = builtins
        .values()
        .find(|entry| entry.operation == dialect::BuiltinOp::IntSub)
        .expect("sub registration");
    assert_ne!((add.type_key)(), (sub.type_key)());

    let mut applications = dialect::builtin_applications().collect::<Vec<_>>();
    applications.sort_by_key(|application| application.identity);
    assert_eq!(applications.len(), 4);
    for application in applications {
        let builtin: &HostBuiltinRegistration = builtins
            .get(&(application.type_key)())
            .unwrap_or_else(|| panic!("unregistered builtin path: {}", application.authored_path));
        assert_eq!(application.arity, builtin.signature.operands.len());
        let operands = builtin
            .signature
            .operands
            .iter()
            .copied()
            .map(sort_name)
            .collect::<Vec<_>>()
            .join(",");
        println!(
            "application={}|path={}|operation={}|signature=({})->{}",
            application.identity,
            application.authored_path,
            builtin.operation.stable_name(),
            operands,
            sort_name(builtin.signature.result),
        );
    }
    println!("runtime_application_calls={calls}");
    println!("runtime_marker_drops={}", dialect::marker_drops());
}

