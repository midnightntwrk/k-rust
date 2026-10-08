//! The regression probes of the reviews and critiques (the design's section 2.4), as oracle
//! definitions: each with the terms that seed its exploration and the queries every model of its
//! axioms makes undefined, which must keep their `\ceil` obligation and get no token.

use super::language::{
    Definition, Pat, app, cons, div, inj, int, int_var, requires_eq, undefined, var,
};

/// What a probe's queries must satisfy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Expect {
    /// Every query keeps its `\ceil` obligation and gets no token.
    Kept,
    /// The definition violates P2: the oracle must detect it.
    OutsideTotality,
    /// The queries' evaluation does not end: the oracle must detect it.
    OutsideTermination,
}

/// One probe: a definition, terms to seed the exploration with, and the queries every model of
/// its axioms makes undefined.
pub(super) struct Probe {
    pub(super) name: String,
    pub(super) definition: Definition,
    pub(super) seeds: Vec<Pat>,
    pub(super) undefined: Vec<Pat>,
    pub(super) expect: Expect,
}

fn probe(name: &str, definition: Definition, seeds: Vec<Pat>, undefined: Vec<Pat>) -> Probe {
    Probe {
        name: name.into(),
        definition,
        seeds,
        undefined,
        expect: Expect::Kept,
    }
}

#[allow(
    clippy::too_many_lines,
    reason = "one probe per reviewed counterexample"
)]
pub(super) fn probes() -> Vec<Probe> {
    let mut probes = Vec::new();
    // Review 1, F1 and F2: `h(3) = h(1)`, `w(h(X)) = mk(X /Int 0) requires X ==Int 3`, and the
    // unconditional `w(h(3)) = mk(1 /Int 0)`.
    let review1 = Definition::new(&["H"])
        .head("h", &["Int"], "H")
        .head("w", &["H"], "S")
        .equation(app("h", vec![int(3)]), app("h", vec![int(1)]));
    probes.push(probe(
        "review 1 F1",
        review1.clone().conditional(
            app("w", vec![app("h", vec![int_var("VarX")])]),
            app("mk", vec![div(int_var("VarX"), int(0))]),
            requires_eq("VarX", 3),
        ),
        vec![],
        vec![
            app("w", vec![app("h", vec![int(1)])]),
            app("w", vec![app("h", vec![int(3)])]),
        ],
    ));
    probes.push(probe(
        "review 1 F2",
        review1.equation(app("w", vec![app("h", vec![int(3)])]), undefined()),
        vec![],
        vec![app("w", vec![app("h", vec![int(1)])])],
    ));
    // Review 2, F1: sorts `B < A < T`; `h(inj{A,T}(X)) = k(X)`, `w(h(inj{B,T}(b0))) = mk(1 /Int 0)`.
    probes.push(probe(
        "review 2 F1",
        Definition::new(&["B", "A", "T", "H"])
            .subsort("B", "A")
            .subsort("A", "T")
            .subsort("B", "T")
            .constructor("b0", &[], "B")
            .constructor("k", &["A"], "H")
            .head("h", &["T"], "H")
            .head("w", &["H"], "S")
            .equation(
                app("h", vec![inj("A", "T", var("VarX", "A"))]),
                app("k", vec![var("VarX", "A")]),
            )
            .equation(
                app("w", vec![app("h", vec![inj("B", "T", cons("b0"))])]),
                undefined(),
            ),
        vec![],
        vec![app("w", vec![app("k", vec![inj("B", "A", cons("b0"))])])],
    ));
    // Round 3: sorts `C < A < T`, `C < B < T`; `g() = inj{C,B}(c0)`.
    probes.push(probe(
        "round 3 common subsort",
        Definition::new(&["C", "A", "B", "T", "H"])
            .subsort("C", "A")
            .subsort("A", "T")
            .subsort("C", "B")
            .subsort("B", "T")
            .subsort("C", "T")
            .constructor("c0", &[], "C")
            .constructor("k", &["A"], "H")
            .head("g", &[], "B")
            .head("h", &["T"], "H")
            .head("w", &["H"], "S")
            .equation(
                app("h", vec![inj("A", "T", var("VarX", "A"))]),
                app("k", vec![var("VarX", "A")]),
            )
            .equation(cons("g"), inj("C", "B", cons("c0")))
            .equation(
                app("w", vec![app("h", vec![inj("B", "T", cons("g"))])]),
                undefined(),
            ),
        vec![],
        vec![app("w", vec![app("k", vec![inj("C", "A", cons("c0"))])])],
    ));
    // Review 2, F2: `g(5) = f(0)`, `h(g(X)) = k2(X)`, `w(h(f(0))) = mk(1 /Int 0)`. `f` is a
    // total function: were `f(0)` undefined, the `g` and `w` equations, which bind their
    // arguments by membership, would state nothing at `g(5)` and `h(f(0))`, and `w(k2(5))`
    // would be undefined only in the models where `f(0)` is defined.
    probes.push(probe(
        "review 2 F2",
        Definition::new(&["G", "H"])
            .constructor("k2", &["Int"], "H")
            .total_function("f", &["Int"], "G")
            .head("g", &["Int"], "G")
            .head("h", &["G"], "H")
            .head("w", &["H"], "S")
            .equation(app("g", vec![int(5)]), app("f", vec![int(0)]))
            .equation(
                app("h", vec![app("g", vec![int_var("VarX")])]),
                app("k2", vec![int_var("VarX")]),
            )
            .equation(
                app("w", vec![app("h", vec![app("f", vec![int(0)])])]),
                undefined(),
            ),
        vec![app("w", vec![app("h", vec![app("g", vec![int(5)])])])],
        vec![app("w", vec![app("k2", vec![int(5)])])],
    ));
    // Review 2, F3: `f(f(inj{K,F}(k(X)))) = c` must not recurse without bound.
    probes.push(probe(
        "review 2 F3",
        Definition::new(&["K", "F"])
            .subsort("K", "F")
            .constructor("k", &["F"], "K")
            .constructor("c", &[], "F")
            .head("f", &["F"], "F")
            .equation(
                app(
                    "f",
                    vec![app(
                        "f",
                        vec![inj("K", "F", app("k", vec![var("VarX", "F")]))],
                    )],
                ),
                cons("c"),
            ),
        vec![app("f", vec![inj("K", "F", app("k", vec![cons("c")]))])],
        vec![],
    ));
    // Review 3, F1, and my round-4 counterexample: `g(5) = c1` and two `f` equations.
    let review3 = Definition::new(&["G"])
        .constructor("c1", &[], "G")
        .constructor("c2", &[], "G")
        .constructor("c3", &[], "G")
        .head("g", &["Int"], "G")
        .head("f", &["G", "Int"], "S")
        .equation(app("g", vec![int(5)]), cons("c1"));
    let z = || int_var("VarZ");
    probes.push(probe(
        "review 3 F1",
        review3
            .clone()
            .equation(
                app("f", vec![cons("c1"), z()]),
                app("f", vec![cons("c2"), z()]),
            )
            .equation(
                app("f", vec![app("g", vec![int_var("VarX")]), z()]),
                undefined(),
            ),
        vec![app("f", vec![app("g", vec![int(5)]), int(0)])],
        vec![app("f", vec![cons("c2"), int(0)])],
    ));
    probes.push(probe(
        "round 4 own root step",
        review3
            .equation(
                app("f", vec![app("g", vec![int_var("VarX")]), z()]),
                app("f", vec![cons("c2"), z()]),
            )
            .equation(app("f", vec![cons("c1"), z()]), undefined()),
        vec![app("f", vec![app("g", vec![int(5)]), int(0)])],
        vec![app("f", vec![cons("c2"), int(0)])],
    ));
    // Review 3, F2: `f(X, Z) = mk(X /Int 0) requires X ==Int 3` and `f(3, Z) = f(1, Z)`.
    probes.push(probe(
        "review 3 F2",
        Definition::new(&[])
            .head("f", &["Int", "Int"], "S")
            .equation(app("f", vec![int(3), z()]), app("f", vec![int(1), z()]))
            .conditional(
                app("f", vec![int_var("VarX"), z()]),
                app("mk", vec![div(int_var("VarX"), int(0))]),
                requires_eq("VarX", 3),
            ),
        vec![],
        vec![app("f", vec![int(1), int(0)])],
    ));
    // Review 4, F1: `O: f(e(Y), W) = f(d(Y), c)`, `P: f(V, k(Y)) = f(d(Y), c)`, and either
    // `f(d(X), c) = mk(X /Int 0) requires X ==Int 3` or `f(d(3), c) = mk(1 /Int 0)`; `P`'s
    // variable named like `O`'s or not.
    for second in ["VarY", "VarU"] {
        let review4 = Definition::new(&["A", "T"])
            .constructor("e", &["Int"], "A")
            .constructor("d", &["Int"], "A")
            .constructor("k", &["Int"], "T")
            .constructor("c", &[], "T")
            .head("f", &["A", "T"], "S")
            .equation(
                app("f", vec![app("e", vec![int_var("VarY")]), var("VarW", "T")]),
                app("f", vec![app("d", vec![int_var("VarY")]), cons("c")]),
            )
            .equation(
                app("f", vec![var("VarV", "A"), app("k", vec![int_var(second)])]),
                app("f", vec![app("d", vec![int_var(second)]), cons("c")]),
            );
        let seeds = vec![app(
            "f",
            vec![app("e", vec![int(1)]), app("k", vec![int(3)])],
        )];
        let query = vec![app("f", vec![app("d", vec![int(1)]), cons("c")])];
        probes.push(probe(
            &format!("review 4 F1 discharge ({second})"),
            review4.clone().conditional(
                app("f", vec![app("d", vec![int_var("VarX")]), cons("c")]),
                app("mk", vec![div(int_var("VarX"), int(0))]),
                requires_eq("VarX", 3),
            ),
            seeds.clone(),
            query.clone(),
        ));
        probes.push(probe(
            &format!("review 4 F1 instance normality ({second})"),
            review4.equation(
                app("f", vec![app("d", vec![int(3)]), cons("c")]),
                undefined(),
            ),
            seeds,
            query,
        ));
    }
    // Round 6, from the random run (seed 0x5eed0006, case 115): `q(q(Y, J), J) = q(q(c, J), J)`
    // overlaps itself below its root, so each round of the pattern facts builds larger overlap
    // representatives from the last; without a bound on their work the rounds exhaust memory.
    probes.push(probe(
        "round 6 self overlap",
        Definition::new(&["A"])
            .constructor("c", &[], "A")
            .constructor("d", &[], "A")
            .constructor("k", &["A"], "A")
            .constructor("j", &["A", "A"], "A")
            .constructor("m", &["Int"], "A")
            .head("g", &["A"], "S")
            .head("q", &["A", "Int"], "A")
            .equation(
                app("g", vec![app("m", vec![int(2)])]),
                app("mk", vec![div(int(3), int(0))]),
            )
            .equation(
                app(
                    "g",
                    vec![app(
                        "q",
                        vec![app("j", vec![cons("c"), cons("c")]), int_var("VarI")],
                    )],
                ),
                app("g", vec![app("k", vec![app("q", vec![cons("d"), int(2)])])]),
            )
            .equation(app("q", vec![cons("d"), int(2)]), app("m", vec![int(2)]))
            .equation(
                app(
                    "q",
                    vec![
                        app("q", vec![var("VarY", "A"), int_var("VarJ")]),
                        int_var("VarJ"),
                    ],
                ),
                app(
                    "q",
                    vec![app("q", vec![cons("c"), int_var("VarJ")]), int_var("VarJ")],
                ),
            ),
        vec![],
        vec![app("g", vec![app("m", vec![int(2)])])],
    ));
    // Round 6, from the random run (seed 0x5eed0006, case 482): `h(q(3, Y)) = 1 /Int 0` and
    // `h(X) = 3` do not meet at `h(q(3, c))`, so the value `q(3, c)` that `h(X) = 3` binds there
    // is undefined, and so is its normal form `g(d)`. The root pair is not joined; `h`, `q` and
    // `g` are tainted.
    probes.push(probe(
        "round 6 bound value",
        Definition::new(&["A"])
            .constructor("c", &[], "A")
            .constructor("d", &[], "A")
            .head("g", &["A"], "A")
            .head("h", &["A"], "Int")
            .head("q", &["Int", "A"], "A")
            .equation(
                app("h", vec![app("q", vec![int(3), var("VarY", "A")])]),
                div(int(1), int(0)),
            )
            .equation(app("h", vec![var("VarX", "A")]), int(3))
            .equation(
                app("q", vec![int_var("VarI"), var("VarX", "A")]),
                app("g", vec![cons("d")]),
            ),
        vec![app("h", vec![app("q", vec![int(3), cons("c")])])],
        vec![app("h", vec![app("g", vec![cons("d")])])],
    ));
    // Review 4, F2: the cross-head example of `docs/compatibility.md` with a conditional `wrap`
    // equation. `wrap(1)` is undefined through the inner pair of the `h` equations at
    // `h(g(5))`; T-sym taints `wrap`, which keeps its obligation.
    probes.push(probe(
        "review 4 F2",
        Definition::new(&["G"])
            .constructor("c1", &[], "G")
            .head("wrap", &["Int"], "S")
            .head("g", &["Int"], "G")
            .head("h", &["G"], "S")
            .conditional(
                app("wrap", vec![int_var("VarX")]),
                app("mk", vec![div(int_var("VarX"), int(0))]),
                requires_eq("VarX", 0),
            )
            .equation(app("g", vec![int(5)]), cons("c1"))
            .equation(app("h", vec![cons("c1")]), app("wrap", vec![int(1)]))
            .equation(app("h", vec![app("g", vec![int_var("VarX")])]), undefined()),
        vec![app("h", vec![app("g", vec![int(5)])])],
        vec![app("wrap", vec![int(1)])],
    ));
    // Round 5 (mine): reducts that keep a variable narrowing leaves unbound, chained and
    // composed, named like the `f` equation's or not.
    for name in ["VarZ", "VarU"] {
        let chained = |first: Pat| {
            Definition::new(&["A"])
                .constructor("k", &["A"], "A")
                .constructor("s", &["A"], "A")
                .constructor("m", &["A"], "A")
                .constructor("m2", &["A"], "A")
                .constructor("c", &[], "A")
                .constructor("d", &[], "A")
                .head("p", &["A", "A"], "A")
                .head("h", &["A", "A"], "A")
                .head("q", &["A", "A", "A"], "A")
                .head("v", &["A"], "A")
                .head("f", &["A"], "S")
                .equation(
                    app("q", vec![first, var("VarX", "A"), var("VarX", "A")]),
                    cons("c"),
                )
                .equation(
                    app(
                        "f",
                        vec![app(
                            "p",
                            vec![var("VarA", "A"), app("s", vec![var("VarZ", "A")])],
                        )],
                    ),
                    undefined(),
                )
        };
        let subject = app("f", vec![app("m", vec![app("m2", vec![cons("c")])])]);
        probes.push(probe(
            &format!("round 5 chained ({name})"),
            chained(cons("c"))
                .equation(
                    app(
                        "p",
                        vec![app("k", vec![var("VarY", "A")]), var("VarV", "A")],
                    ),
                    app(
                        "m",
                        vec![app("h", vec![var("VarY", "A"), var("VarV", "A")])],
                    ),
                )
                .equation(
                    app("h", vec![app("k", vec![var(name, "A")]), var("VarV", "A")]),
                    app(
                        "m2",
                        vec![app(
                            "q",
                            vec![var(name, "A"), var("VarV", "A"), app("s", vec![cons("d")])],
                        )],
                    ),
                ),
            vec![app(
                "f",
                vec![app(
                    "p",
                    vec![
                        app("k", vec![app("k", vec![cons("c")])]),
                        app("s", vec![cons("d")]),
                    ],
                )],
            )],
            vec![subject.clone()],
        ));
        probes.push(probe(
            &format!("round 5 composed ({name})"),
            chained(app("k", vec![cons("c")]))
                .equation(
                    app(
                        "p",
                        vec![app("k", vec![var("VarY", "A")]), var("VarV", "A")],
                    ),
                    app("m", vec![app("h", vec![cons("c"), var("VarV", "A")])]),
                )
                .equation(
                    app(
                        "h",
                        vec![app("v", vec![var("VarX", "A")]), var("VarV", "A")],
                    ),
                    app(
                        "m2",
                        vec![app(
                            "q",
                            vec![
                                var("VarX", "A"),
                                var("VarV", "A"),
                                app("s", vec![cons("d")]),
                            ],
                        )],
                    ),
                )
                .equation(app("v", vec![app("k", vec![var(name, "A")])]), cons("c")),
            vec![
                app(
                    "f",
                    vec![app(
                        "p",
                        vec![app("k", vec![cons("c")]), app("s", vec![cons("d")])],
                    )],
                ),
                app(
                    "f",
                    vec![app(
                        "m",
                        vec![app(
                            "h",
                            vec![
                                app("v", vec![app("k", vec![cons("c")])]),
                                app("s", vec![cons("d")]),
                            ],
                        )],
                    )],
                ),
            ],
            vec![subject],
        ));
    }
    // Review 5, F1: `canonical` names. `H`'s first variable named like `G`'s or not; with and
    // without the conditional `D`.
    for name in ["VarY", "VarU"] {
        for discharge in [false, true] {
            let mut definition = Definition::new(&["A"])
                .constructor("n", &["A"], "A")
                .constructor("k", &["A"], "A")
                .constructor("j", &["A", "A"], "A")
                .constructor("m", &["Int"], "A")
                .constructor("c", &[], "A")
                .constructor("d", &[], "A")
                .head("q", &["A", "A", "A"], "Int")
                .head("f", &["A", "A"], "S")
                .equation(
                    app(
                        "q",
                        vec![
                            cons("c"),
                            app("n", vec![app("n", vec![cons("c")])]),
                            cons("d"),
                        ],
                    ),
                    int(0),
                )
                .equation(
                    app(
                        "f",
                        vec![var("VarV", "A"), app("k", vec![var("VarY", "A")])],
                    ),
                    app(
                        "f",
                        vec![
                            var("VarV", "A"),
                            app("j", vec![var("VarV", "A"), var("VarY", "A")]),
                        ],
                    ),
                )
                .equation(
                    app(
                        "f",
                        vec![
                            app("n", vec![var("VarY", "A")]),
                            app("k", vec![var("VarW", "A")]),
                        ],
                    ),
                    undefined(),
                )
                .equation(
                    app(
                        "f",
                        vec![
                            app("n", vec![app("n", vec![var(name, "A")])]),
                            app("j", vec![var("VarW", "A"), var("VarY2", "A")]),
                        ],
                    ),
                    app(
                        "f",
                        vec![
                            app(
                                "m",
                                vec![app(
                                    "q",
                                    vec![var(name, "A"), var("VarW", "A"), var("VarY2", "A")],
                                )],
                            ),
                            cons("c"),
                        ],
                    ),
                );
            if discharge {
                definition = definition.conditional(
                    app("f", vec![app("m", vec![int_var("VarX")]), cons("c")]),
                    app("mk", vec![div(int_var("VarX"), int(0))]),
                    requires_eq("VarX", 3),
                );
            }
            probes.push(probe(
                &format!("review 5 F1 ({name}, discharge {discharge})"),
                definition,
                vec![app(
                    "f",
                    vec![
                        app("n", vec![app("n", vec![cons("c")])]),
                        app("k", vec![cons("d")]),
                    ],
                )],
                vec![app("f", vec![app("m", vec![int(0)]), cons("c")])],
            ));
        }
    }
    // Review 5, F2: the bound fallback; `count` pairs of constructors, with and without `D`.
    for count in [3, 70] {
        for discharge in [false, true] {
            let mut definition = Definition::new(&["A"])
                .constructor("m", &["Int"], "A")
                .constructor("c1", &[], "A")
                .constructor("c2", &[], "A");
            for index in 0..count {
                definition = definition
                    .constructor(&format!("n{index}"), &["A"], "A")
                    .constructor(&format!("s{index}"), &["A"], "A");
            }
            definition = definition
                .head("v", &["A"], "A")
                .head("p", &["A", "A"], "A")
                .head("r", &["A", "A"], "Int")
                .head("f", &["A"], "S");
            for index in 0..count {
                definition = definition.equation(
                    app("v", vec![app(&format!("n{index}"), vec![var("VarZ", "A")])]),
                    app(&format!("s{index}"), vec![var("VarZ", "A")]),
                );
            }
            definition = definition
                .equation(
                    app(
                        "p",
                        vec![
                            app("s0", vec![var("VarA", "A")]),
                            app("s0", vec![var("VarB", "A")]),
                        ],
                    ),
                    app(
                        "m",
                        vec![app("r", vec![var("VarA", "A"), var("VarB", "A")])],
                    ),
                )
                .equation(app("r", vec![cons("c1"), cons("c2")]), int(0))
                .equation(
                    app(
                        "f",
                        vec![app(
                            "p",
                            vec![
                                app("v", vec![var("VarW1", "A")]),
                                app("v", vec![var("VarW2", "A")]),
                            ],
                        )],
                    ),
                    undefined(),
                );
            if discharge {
                definition = definition.conditional(
                    app("f", vec![app("m", vec![int_var("VarX")])]),
                    app("mk", vec![div(int_var("VarX"), int(0))]),
                    requires_eq("VarX", 3),
                );
            }
            probes.push(probe(
                &format!("review 5 F2 (count {count}, discharge {discharge})"),
                definition,
                vec![app(
                    "f",
                    vec![app(
                        "p",
                        vec![
                            app("v", vec![app("n0", vec![cons("c1")])]),
                            app("v", vec![app("n0", vec![cons("c2")])]),
                        ],
                    )],
                )],
                vec![app("f", vec![app("m", vec![int(0)])])],
            ));
        }
    }
    // Round 7, from the random run with total heads (seed 0x5eed0006, case 2466, minimized):
    // `e(f(X)) = m(1 /Int 0)` with `e` total makes `f(c)` undefined, without any pair: the
    // definition violates P2 (a total symbol undefined on defined arguments), which the oracle
    // detects and counts.
    probes.push(Probe {
        expect: Expect::OutsideTotality,
        ..probe(
            "round 7 total head of another equation",
            Definition::new(&["A"])
                .constructor("c", &[], "A")
                .constructor("m", &["Int"], "A")
                .total_head("e", &["A"], "A")
                .head("f", &["A"], "A")
                .equation(
                    app("e", vec![app("f", vec![var("VarX", "A")])]),
                    app("m", vec![div(int(1), int(0))]),
                ),
            vec![],
            vec![app("f", vec![cons("c")])],
        )
    });
    // Round 7, from the random run with total heads (seed 0x5eed0006, case 16195, minimized):
    // the peak of `g(X, 3) = f(c)` and `g(k(d), 3) = m(2 /Int 0)` at `g(k(d), 3)` makes `f(c)`
    // undefined. The equation `g(g(f(c), 0), 1) = k(g(g(d, 2), 0))` binds its first argument by
    // membership in `g(f(c), 0)`, which is then undefined, so it states nothing, and some model
    // defines `g(g(d, 2), 0)`. Round 7 read the ground equation as an equality between its
    // sides and excused the backend's claims on `g(g(d, 2), 0)`.
    // `f(c)` itself is undefined through the root pair of the two `g` equations at
    // `g(k(d), 3)`, which is not joined; `g` and `f` are tainted.
    probes.push(probe(
        "round 7 vacuous left-hand side",
        Definition::new(&["A"])
            .constructor("c", &[], "A")
            .constructor("d", &[], "A")
            .constructor("k", &["A"], "A")
            .constructor("m", &["Int"], "A")
            .head("f", &["A"], "A")
            .head("g", &["A", "Int"], "A")
            .equation(
                app(
                    "g",
                    vec![app("g", vec![app("f", vec![cons("c")]), int(0)]), int(1)],
                ),
                app(
                    "k",
                    vec![app("g", vec![app("g", vec![cons("d"), int(2)]), int(0)])],
                ),
            )
            .equation(
                app("g", vec![var("VarX", "A"), int(3)]),
                app("f", vec![cons("c")]),
            )
            .equation(
                app("g", vec![app("k", vec![cons("d")]), int(3)]),
                app("m", vec![div(int(2), int(0))]),
            ),
        vec![
            app("g", vec![app("k", vec![cons("d")]), int(3)]),
            app("g", vec![app("g", vec![cons("d"), int(2)]), int(0)]),
        ],
        vec![app("f", vec![cons("c")])],
    ));
    // Review 7, F1: `f(m(I)) = c requires I ==Int 0` is refuted at `f(m(1))`, and `e(f(m(1))) =
    // m(1 /Int 0)` with `e` total makes `f(m(1))` undefined without any pair: in `M_NF`, `f(m(1))`
    // is a stuck head application, a value, and the total `e` is undefined on it, so the
    // definition violates P2, which the oracle detects and counts (the design's 2.4).
    let conditional_f = Definition::new(&["A"])
        .constructor("c", &[], "A")
        .constructor("k", &["A"], "A")
        .constructor("m", &["Int"], "A")
        .total_head("e", &["A"], "A")
        .head("f", &["A"], "A")
        .head("q", &["A"], "A")
        .conditional(
            app("f", vec![app("m", vec![int_var("VarI")])]),
            cons("c"),
            requires_eq("VarI", 0),
        );
    let f_m_1 = app("f", vec![app("m", vec![int(1)])]);
    probes.push(Probe {
        expect: Expect::OutsideTotality,
        ..probe(
            "review 7 F1",
            conditional_f.clone().equation(
                app("e", vec![f_m_1.clone()]),
                app("m", vec![div(int(1), int(0))]),
            ),
            vec![],
            vec![f_m_1.clone()],
        )
    });
    // Round 8: `q(c) = k(f(m(1)))` beside `q(c) = m(1 /Int 0)` makes `f(m(1))` undefined through
    // the root pair of `q`, which is not joined; T-sym taints `f`.
    probes.push(probe(
        "round 8 right-hand side of another head",
        conditional_f
            .equation(app("q", vec![cons("c")]), app("k", vec![f_m_1.clone()]))
            .equation(
                app("q", vec![cons("c")]),
                app("m", vec![div(int(1), int(0))]),
            ),
        vec![],
        vec![f_m_1],
    ));
    // Review 6, F1 and F2: `e : A -> A` a total equation head, `sz : A -> Int` a total
    // function; `g(d) = m(1 /Int 0)` beside `g(d) = C[g(t)]` with `C` built from total symbols
    // only, so `g(t)` is undefined; F1 adds `g(m(I)) = c requires I ==Int 0`, refuted at
    // `g(m(1))`.
    for (label, held, conditional) in [
        ("F1", app("g", vec![app("m", vec![int(1)])]), true),
        ("F2", app("g", vec![app("s", vec![cons("c")])]), false),
    ] {
        for (context, second) in [
            ("k(e(_))", app("k", vec![app("e", vec![held.clone()])])),
            ("e(_)", app("e", vec![held.clone()])),
            ("m(sz(_))", app("m", vec![app("sz", vec![held.clone()])])),
            ("k(_)", app("k", vec![held.clone()])),
        ] {
            let mut definition = Definition::new(&["A"])
                .constructor("c", &[], "A")
                .constructor("d", &[], "A")
                .constructor("k", &["A"], "A")
                .constructor("s", &["A"], "A")
                .constructor("m", &["Int"], "A")
                .total_head("e", &["A"], "A")
                .total_function("sz", &["A"], "Int")
                .head("g", &["A"], "A")
                .equation(
                    app("g", vec![cons("d")]),
                    app("m", vec![div(int(1), int(0))]),
                )
                .equation(app("g", vec![cons("d")]), second);
            if conditional {
                definition = definition.conditional(
                    app("g", vec![app("m", vec![int_var("VarI")])]),
                    cons("c"),
                    requires_eq("VarI", 0),
                );
            }
            probes.push(probe(
                &format!("review 6 {label} ({context})"),
                definition,
                vec![],
                vec![held.clone()],
            ));
        }
    }
    // Review 2 (pre-existing): the root pair `g(1) = f(0)`, `g(X) = mk(1 /Int 0)`.
    probes.push(probe(
        "review 2 root pair",
        Definition::new(&[])
            .head("f", &["Int"], "S")
            .head("g", &["Int"], "S")
            .equation(app("g", vec![int(1)]), app("f", vec![int(0)]))
            .equation(app("g", vec![int_var("VarX")]), undefined()),
        vec![app("g", vec![int(1)])],
        vec![app("f", vec![int(0)])],
    ));
    // Review 4, the limit: `g(5) = c1`; `f(c1) = k(0)`; `f(g(X)) = mk(1 /Int 0)`.
    probes.push(probe(
        "review 4 limit",
        Definition::new(&["G"])
            .constructor("c1", &[], "G")
            .head("k", &["Int"], "S")
            .head("g", &["Int"], "G")
            .head("f", &["G"], "S")
            .equation(app("g", vec![int(5)]), cons("c1"))
            .equation(app("f", vec![cons("c1")]), app("k", vec![int(0)]))
            .equation(app("f", vec![app("g", vec![int_var("VarX")])]), undefined()),
        vec![app("f", vec![app("g", vec![int(5)])])],
        vec![app("k", vec![int(0)])],
    ));
    // Review 8, the limit: `h(m(I), Y) = Y requires I ==Int 0`; `g(h(m(0), Y)) = mk(1 /Int 0)`.
    probes.push(probe(
        "review 8 limit",
        Definition::new(&["A"])
            .constructor("c", &[], "A")
            .constructor("m", &["Int"], "A")
            .head("h", &["A", "A"], "A")
            .head("g", &["A"], "S")
            .conditional(
                app("h", vec![app("m", vec![int_var("VarI")]), var("VarY", "A")]),
                var("VarY", "A"),
                requires_eq("VarI", 0),
            )
            .equation(
                app(
                    "g",
                    vec![app("h", vec![app("m", vec![int(0)]), var("VarY", "A")])],
                ),
                undefined(),
            ),
        vec![app(
            "g",
            vec![app("h", vec![app("m", vec![int(0)]), cons("c")])],
        )],
        vec![app("g", vec![cons("c")])],
    ));
    // CV minor 1: `a = b`, `a = d`, `b = a`, `b = c`: no normal form is reached from `a` on
    // every path, so the component is outside P0, which the oracle detects and counts.
    probes.push(Probe {
        expect: Expect::OutsideTermination,
        ..probe(
            "CV minor 1",
            Definition::new(&["A"])
                .constructor("c", &[], "A")
                .constructor("d", &[], "A")
                .head("a", &[], "A")
                .head("b", &[], "A")
                .equation(cons("a"), cons("b"))
                .equation(cons("a"), cons("d"))
                .equation(cons("b"), cons("a"))
                .equation(cons("b"), cons("c")),
            vec![],
            vec![cons("a")],
        )
    });
    probes
}
