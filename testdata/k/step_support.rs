//! Reusable declarations over the complete generated configuration.
#![allow(dead_code)]

use k_rust::kore::ast::Pattern;
use kink_native::step_events::StepEventSpec;

use crate::support;

fn variable(name: &str, sort: &str) -> Pattern {
    support::var(name, sort)
}

fn application(symbol: &str, arguments: Vec<Pattern>) -> Pattern {
    support::app(symbol, arguments)
}

fn sequence(operation: Pattern, continuation: Pattern) -> Pattern {
    application("Lblseq", vec![operation, continuation])
}

fn config(program: Pattern, sort: &str, counter: &str) -> Pattern {
    support::k_config(program, sort, "R", counter)
}

fn declaration(
    constructor: &str,
    pre: Pattern,
    post: Option<Pattern>,
    payload: &[&str],
) -> StepEventSpec {
    StepEventSpec {
        constructor: constructor.into(),
        pre,
        post,
        payload: payload.iter().map(|name| (*name).into()).collect(),
    }
}

/// Symmem write, load and free, in that declaration order.
pub fn symmem(whole_transition: bool) -> Vec<StepEventSpec> {
    let mut specs = Vec::new();
    for (constructor, symbol, include_value) in [
        ("memoryWrite", "Lblwrite", true),
        ("memoryLoad", "Lblload", true),
        ("memoryFree", "Lblfree", false),
    ] {
        let mut arguments = vec![variable("A", "SortAddress")];
        if include_value {
            arguments.push(variable("V", "SortNat"));
        }
        let pre = config(
            sequence(application(symbol, arguments), variable("P", "SortProg")),
            "SortProg",
            "C",
        );
        let post = whole_transition.then(|| config(variable("P", "SortProg"), "SortProg", "C2"));
        specs.push(declaration(
            constructor,
            pre,
            post,
            if include_value { &["A", "V"] } else { &["A"] },
        ));
    }
    specs
}

/// Guarded memory's write, load and negative-load declarations.
pub fn guardedmem(whole_transition: bool) -> Vec<StepEventSpec> {
    [
        ("memoryWrite", "Lblwrite"),
        ("memoryLoad", "Lblload"),
        ("memoryLoad", "LblloadNeg"),
    ]
    .into_iter()
    .map(|(constructor, symbol)| {
        let operation = application(
            symbol,
            vec![
                application("Lbladdr", vec![variable("A", "SortInt")]),
                variable("V", "SortInt"),
            ],
        );
        declaration(
            constructor,
            config(
                sequence(operation, variable("P", "SortProg")),
                "SortProg",
                "C",
            ),
            whole_transition.then(|| config(variable("P", "SortProg"), "SortProg", "C2")),
            &["A", "V"],
        )
    })
    .collect()
}

/// Freshgen write observes its stamped continuation; load observes its ordinary continuation.
pub fn freshgen(whole_transition: bool) -> Vec<StepEventSpec> {
    ["Lblwrite", "Lblload"]
        .into_iter()
        .map(|symbol| {
            let constructor = if symbol == "Lblwrite" {
                "memoryWrite"
            } else {
                "memoryLoad"
            };
            let operation = application(
                symbol,
                vec![
                    application("Lbladdr", vec![variable("A", "SortInt")]),
                    variable("V", "SortInt"),
                ],
            );
            let continuation = variable("P", "SortProg");
            let post_program = if symbol == "Lblwrite" {
                sequence(
                    application("Lblstamp", vec![variable("T", "SortInt")]),
                    continuation,
                )
            } else {
                continuation
            };
            declaration(
                constructor,
                config(
                    sequence(operation, variable("P", "SortProg")),
                    "SortProg",
                    "C",
                ),
                whole_transition.then(|| config(post_program, "SortProg", "C2")),
                &["A", "V"],
            )
        })
        .collect()
}

/// Counter increments and the true branch of choose.
pub fn counter(whole_transition: bool) -> Vec<StepEventSpec> {
    let n = || variable("N", "SortNat");
    let l = || variable("L", "SortNat");
    let increment = declaration(
        "increment",
        config(
            application("Lblcounter", vec![n(), application("Lbls", vec![l()])]),
            "SortCounter",
            "C",
        ),
        whole_transition.then(|| {
            config(
                application("Lblcounter", vec![application("Lbls", vec![n()]), l()]),
                "SortCounter",
                "C2",
            )
        }),
        &[],
    );
    let truth = Pattern::DomainValue {
        sort: k_rust::kompile::initial_configuration::kore_sort("SortBool"),
        value: "true".into(),
    };
    let branch = declaration(
        "branchTaken",
        config(
            application("Lblchoose", vec![truth.clone()]),
            "SortControl",
            "C",
        ),
        whole_transition
            .then(|| config(application("Lblselected", vec![truth]), "SortControl", "C2")),
        &[],
    );
    vec![increment, branch]
}
