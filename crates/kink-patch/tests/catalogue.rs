//! Catalogue order and codec pins. The fixture label pins and the deterministic candidate sweep
//! over the fixture definitions are in sweep.rs.

use kink_patch::{Action, Clause, OperatorSpec, catalogue_v1};
use std::collections::BTreeSet;

#[test]
fn catalogue_order_and_all_codecs_are_pinned() {
    let specs = catalogue_v1();
    assert_eq!(specs.len(), 63);
    let groups = [
        ("cond-true", 1),
        ("cond-false", 1),
        ("cond-negate", 1),
        ("not-unwrap", 1),
        ("ror", 30),
        ("aor", 20),
        ("lcr", 2),
        ("eqk", 2),
        ("int-literal", 2),
        ("drop-owise", 1),
        ("drop-priority", 1),
        ("delete-rule", 1),
    ];
    let expected_ids = groups
        .into_iter()
        .flat_map(|(id, count)| std::iter::repeat_n(id, count))
        .collect::<Vec<_>>();
    assert_eq!(
        specs.iter().map(OperatorSpec::id).collect::<Vec<_>>(),
        expected_ids
    );
    assert_eq!(
        specs
            .iter()
            .map(OperatorSpec::name)
            .collect::<BTreeSet<_>>()
            .len(),
        63
    );
    for spec in &specs {
        assert_eq!(spec.version(), 1);
        let text = spec.canonical_json();
        let decoded = OperatorSpec::from_canonical_json(&text).expect("catalogue decodes");
        assert_eq!(&decoded, spec);
        assert_eq!(decoded.canonical_json(), text);
        assert_eq!(decoded.digest(), spec.digest());
    }
    for (id, labels) in [
        (
            "ror",
            [
                "_<Int_", "_<=Int_", "_>Int_", "_>=Int_", "_==Int_", "_=/=Int_",
            ]
            .as_slice(),
        ),
        (
            "aor",
            ["_+Int_", "_-Int_", "_*Int_", "_/Int_", "_%Int_"].as_slice(),
        ),
        ("lcr", ["_andBool_", "_orBool_"].as_slice()),
        ("eqk", ["_==K_", "_=/=K_"].as_slice()),
    ] {
        let expected = labels
            .iter()
            .flat_map(|from| {
                labels
                    .iter()
                    .filter(move |to| from != *to)
                    .map(move |to| (*from, *to))
            })
            .collect::<Vec<_>>();
        let actual = specs
            .iter()
            .filter(|spec| spec.id() == id)
            .map(|spec| {
                let [Clause::Head { label }] = spec.selector() else {
                    panic!("pair head selector")
                };
                let Action::ReplaceHead { to } = spec.action() else {
                    panic!("pair replacement")
                };
                assert_eq!(spec.variant(), format!("{label}->{to}"));
                (label.as_str(), to.as_str())
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, expected);
    }
    assert_eq!(specs[58].variant(), "+1");
    assert_eq!(specs[59].variant(), "-1");
}

#[test]
fn cond_true_v1_has_an_independent_known_answer() {
    // Independently computed with Python hashlib: domain UTF-8, NUL, canonical bytes.
    const BYTES: &str = r#"{"action":{"replace-with-token":{"sort":"Bool","token":"true"}},"id":"cond-true","policy":"each","selector":[{"path":[1]},{"not-token":{"sort":"Bool","token":"true"}}],"variant":"1","version":1}"#;
    const DIGEST: &str = "576790b100cbd01d3b28759dd70e68e725716b6e6660c5869108c7c2be02799c";
    let spec = &catalogue_v1()[0];
    assert_eq!(spec.canonical_json(), BYTES);
    assert_eq!(spec.digest().to_string(), DIGEST);
    assert_eq!(
        OperatorSpec::from_canonical_json(BYTES).expect("known answer decodes"),
        *spec
    );
}
