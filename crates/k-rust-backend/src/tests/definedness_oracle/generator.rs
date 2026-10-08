//! Random definitions and one fixed template per feature class.

use std::collections::BTreeMap;

use super::{
    Rng,
    language::{
        Definition, Kind, OWISE_PRIORITY, Pat, Symbol, app, cons, div, inj, int, int_equals,
        int_var, list, pattern_variables, undefined, var,
    },
};

const A_VARIABLES: [&str; 3] = ["VarX", "VarY", "VarZ"];
const INT_VARIABLES: [&str; 2] = ["VarI", "VarJ"];

struct Generator<'r> {
    rng: &'r mut Rng,
    /// Symbols with equations: equation heads and partial functions.
    heads: Vec<Symbol>,
    /// Symbols that occur in right-hand sides only: total functions.
    functions: Vec<Symbol>,
    /// Whether the sort `B < A` (constructors `b0`, `bk`) is declared.
    subsorts: bool,
    /// Whether the total Boolean function `isc` is declared.
    predicate: bool,
    /// Whether left-hand sides hold no application of an equation head below the root and no
    /// two equations of one head overlap at the root: such definitions have no critical pair.
    orthogonal: bool,
}

impl Generator<'_> {
    fn heads_of(&self, sort: &str) -> Vec<Symbol> {
        self.heads
            .iter()
            .filter(|head| head.result == sort)
            .cloned()
            .collect()
    }

    fn application(
        &mut self,
        head: &Symbol,
        depth: usize,
        left: bool,
        scope: &BTreeMap<String, String>,
    ) -> Pat {
        let arguments = head
            .arguments
            .iter()
            .map(|sort| {
                if left {
                    self.left(sort, depth.saturating_sub(1))
                } else {
                    self.right(sort, depth.saturating_sub(1), scope)
                }
            })
            .collect();
        app(&head.name, arguments)
    }

    /// A left-hand side argument of sort `sort`.
    fn left(&mut self, sort: &str, depth: usize) -> Pat {
        let nested = self.heads_of(sort);
        if depth > 0 && !nested.is_empty() && !self.orthogonal && self.rng.percent(15) {
            let head = self.rng.pick(&nested).clone();
            return self.application(&head, depth, true, &BTreeMap::new());
        }
        match sort {
            "Int" => {
                if self.rng.percent(55) {
                    int_var(self.rng.pick::<&str>(&INT_VARIABLES))
                } else {
                    int(i64::try_from(self.rng.below(4)).unwrap())
                }
            }
            _ => {
                if self.rng.percent(35) {
                    return var(self.rng.pick::<&str>(&A_VARIABLES), "A");
                }
                if self.subsorts && self.rng.percent(20) {
                    return if self.rng.percent(50) {
                        inj("B", "A", var("VarB", "B"))
                    } else {
                        inj("B", "A", cons("b0"))
                    };
                }
                if depth > 0 && self.rng.percent(8) {
                    let inner = self.left("A", depth - 1);
                    let alias = self.rng.pick::<&str>(&["VarW", "VarX"]);
                    return Pat::As(
                        Box::new(app("k", vec![inner])),
                        (*alias).to_owned(),
                        "A".into(),
                    );
                }
                self.constructor_term(depth, |generator, sort, depth| generator.left(sort, depth))
            }
        }
    }

    fn constructor_term(
        &mut self,
        depth: usize,
        mut argument: impl FnMut(&mut Self, &str, usize) -> Pat,
    ) -> Pat {
        if depth == 0 || self.rng.percent(30) {
            return cons(self.rng.pick::<&str>(&["c", "d"]));
        }
        match self.rng.below(4) {
            0 => app("n", vec![argument(self, "A", depth - 1)]),
            1 => app("k", vec![argument(self, "A", depth - 1)]),
            2 => app(
                "j",
                vec![
                    argument(self, "A", depth - 1),
                    argument(self, "A", depth - 1),
                ],
            ),
            _ => app("m", vec![argument(self, "Int", depth - 1)]),
        }
    }

    /// A right-hand side term of sort `sort` over the variables `scope`.
    fn right(&mut self, sort: &str, depth: usize, scope: &BTreeMap<String, String>) -> Pat {
        let in_scope = scope
            .iter()
            .filter(|(_, variable_sort)| *variable_sort == sort)
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        let heads = self.heads_of(sort);
        if depth > 0 && !heads.is_empty() && self.rng.percent(30) {
            let head = self.rng.pick(&heads).clone();
            return self.application(&head, depth, false, scope);
        }
        let functions = self
            .functions
            .iter()
            .filter(|function| function.result == sort)
            .cloned()
            .collect::<Vec<_>>();
        if depth > 0 && !functions.is_empty() && self.rng.percent(15) {
            let function = self.rng.pick(&functions).clone();
            return self.application(&function, depth, false, scope);
        }
        match sort {
            "S" => {
                let argument = if depth > 0 && self.rng.percent(40) {
                    let dividend = self.right("Int", depth - 1, scope);
                    let divisor = self.divisor(scope);
                    div(dividend, divisor)
                } else {
                    self.right("Int", depth.saturating_sub(1), scope)
                };
                app("mk", vec![argument])
            }
            "Int" => {
                if !in_scope.is_empty() && self.rng.percent(50) {
                    int_var(self.rng.pick(&in_scope).as_str())
                } else if depth > 0 && self.rng.percent(10) {
                    let dividend = self.right("Int", depth - 1, scope);
                    let divisor = self.divisor(scope);
                    div(dividend, divisor)
                } else {
                    int(i64::try_from(self.rng.below(4)).unwrap())
                }
            }
            "B" => {
                if !in_scope.is_empty() && self.rng.percent(50) {
                    var(self.rng.pick(&in_scope).as_str(), "B")
                } else {
                    cons("b0")
                }
            }
            _ => {
                if !in_scope.is_empty() && self.rng.percent(35) {
                    return var(self.rng.pick(&in_scope).as_str(), "A");
                }
                let b_scope = scope
                    .iter()
                    .filter(|(_, sort)| *sort == "B")
                    .map(|(name, _)| name.clone())
                    .collect::<Vec<_>>();
                if !b_scope.is_empty() && self.rng.percent(25) {
                    return inj("B", "A", var(self.rng.pick(&b_scope).as_str(), "B"));
                }
                self.constructor_term(depth, |generator, sort, depth| {
                    generator.right(sort, depth, scope)
                })
            }
        }
    }

    fn divisor(&mut self, scope: &BTreeMap<String, String>) -> Pat {
        let integers = scope
            .iter()
            .filter(|(_, sort)| *sort == "Int")
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        if integers.is_empty() || self.rng.percent(60) {
            int(0)
        } else {
            int_var(self.rng.pick(&integers).as_str())
        }
    }

    /// A `requires` over the left-hand side's variables, if one fits.
    fn requires(&mut self, scope: &BTreeMap<String, String>) -> Option<Pat> {
        let integers = scope
            .iter()
            .filter(|(_, sort)| *sort == "Int")
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        let terms = scope
            .iter()
            .filter(|(_, sort)| *sort == "A")
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        if self.predicate && !terms.is_empty() && self.rng.percent(30) {
            let term = var(self.rng.pick(&terms).as_str(), "A");
            let test = app("isc", vec![term]);
            return Some(if self.rng.percent(50) {
                test
            } else {
                app("notBool", vec![test])
            });
        }
        if integers.is_empty() {
            return None;
        }
        let variable = int_var(self.rng.pick(&integers).as_str());
        let value = int(i64::try_from(self.rng.below(4)).unwrap());
        Some(match self.rng.below(7) {
            0 => int_equals(variable, value),
            1 => app("ltInt", vec![variable, value]),
            2 => app("leInt", vec![variable, value]),
            3 => app("gtInt", vec![variable, value]),
            4 => app("geInt", vec![variable, value]),
            5 => app("neInt", vec![variable, value]),
            _ => app("notBool", vec![int_equals(variable, value)]),
        })
    }
}

/// A random definition: the base sort `A` with free constructors, two to four equation heads
/// with random equations, and a random selection of the feature templates.
pub(super) fn random_definition(rng: &mut Rng) -> (Definition, Vec<Pat>) {
    let no_head = rng.percent(12);
    let names = ["f", "g", "h", "q"];
    let count = if no_head { 0 } else { 2 + rng.below(3) };
    let mut heads = Vec::new();
    for name in &names[..count] {
        let result = if rng.percent(45) { "S" } else { "A" };
        let arity = match rng.below(100) {
            0..45 => 1,
            45..90 => 2,
            _ => 3,
        };
        let arguments = (0..arity)
            .map(|_| if rng.percent(70) { "A" } else { "Int" }.to_owned())
            .collect();
        heads.push(Symbol {
            name: (*name).into(),
            arguments,
            result: result.into(),
            kind: Kind::Head {
                value_production: rng.percent(85),
                total: false,
            },
        });
    }
    let mut functions = Vec::new();
    if !no_head && rng.percent(35) {
        heads.push(Symbol {
            name: "e".into(),
            arguments: vec!["A".into()],
            result: "A".into(),
            kind: Kind::Head {
                value_production: false,
                total: true,
            },
        });
    }
    if no_head || rng.percent(30) {
        heads.push(Symbol {
            name: "pf".into(),
            arguments: vec!["A".into()],
            result: "A".into(),
            kind: Kind::Function { total: false },
        });
    }
    if rng.percent(25) {
        functions.push(Symbol {
            name: "sz".into(),
            arguments: vec!["A".into()],
            result: "A".into(),
            kind: Kind::Function { total: true },
        });
    }
    let subsorts = rng.percent(25);
    let predicate = rng.percent(20);
    let mut definition = Definition::new(&["A"])
        .constructor("c", &[], "A")
        .constructor("d", &[], "A")
        .constructor("n", &["A"], "A")
        .constructor("k", &["A"], "A")
        .constructor("j", &["A", "A"], "A")
        .constructor("m", &["Int"], "A");
    if subsorts {
        definition = definition
            .subsort("B", "A")
            .constructor("b0", &[], "B")
            .constructor("bk", &["A"], "B");
        definition.sorts.push("B".into());
    }
    if predicate {
        definition = definition
            .total_function("isc", &["A"], "Bool")
            .equation(app("isc", vec![cons("c")]), boolean(true))
            .full(
                app("isc", vec![var("VarX", "A")]),
                boolean(false),
                None,
                None,
                OWISE_PRIORITY,
            );
    }
    definition.symbols.extend(heads.iter().cloned());
    definition.symbols.extend(functions.iter().cloned());
    let orthogonal = rng.percent(50);
    let mut generator = Generator {
        rng,
        heads,
        functions,
        subsorts,
        predicate,
        orthogonal,
    };
    let equations = 2 + generator.rng.below(4);
    let mut previous: Option<Symbol> = None;
    for _ in 0..equations {
        if generator.heads.is_empty() {
            break;
        }
        let head = match &previous {
            Some(head) if generator.rng.percent(30) => head.clone(),
            _ => generator.rng.pick(&generator.heads).clone(),
        };
        let lhs = generator.application(&head, 3, true, &BTreeMap::new());
        if generator.orthogonal
            && definition
                .equations
                .iter()
                .any(|equation| compatible(&equation.lhs, &lhs))
        {
            continue;
        }
        let mut scope = BTreeMap::new();
        pattern_variables(&lhs, &mut scope);
        let rhs = generator.right(&head.result, 3, &scope);
        let requires = if generator.rng.percent(35) {
            generator.requires(&scope)
        } else {
            None
        };
        let ensures = if generator.rng.percent(10) {
            generator.requires(&scope)
        } else {
            None
        };
        let priority = match generator.rng.below(100) {
            0..8 => 40,
            8..15 => OWISE_PRIORITY,
            _ => super::language::DEFAULT_PRIORITY,
        };
        definition = definition.full(lhs, rhs, requires, ensures, priority);
        previous = Some(head);
    }
    let mut seeds = Vec::new();
    let rng = generator.rng;
    if rng.percent(15) {
        let (with, extra) = lists(definition, rng.percent(50));
        definition = with;
        seeds.extend(extra);
    }
    if rng.percent(15) {
        let (with, extra) = family(definition, rng.percent(50));
        definition = with;
        seeds.extend(extra);
    }
    if rng.percent(8) {
        let (with, extra) = diamond(definition, rng.percent(50));
        definition = with;
        seeds.extend(extra);
    }
    if rng.percent(8) {
        let (with, extra) = non_confluent_family(definition);
        definition = with;
        seeds.extend(extra);
    }
    if rng.percent(15) {
        let (with, extra) = irrelevant_cluster(definition);
        definition = with;
        seeds.extend(extra);
    }
    if !no_head && rng.percent(7) {
        let (with, extra) = erasing(definition);
        definition = with;
        seeds.extend(extra);
    }
    if !no_head && rng.percent(10) {
        let (with, extra) = observation(definition, rng.percent(35));
        definition = with;
        seeds.extend(extra);
    }
    if !no_head && rng.percent(6) {
        let (with, extra) = through_total_function(definition);
        definition = with;
        seeds.extend(extra);
    }
    if !no_head && rng.percent(8) {
        let wrapper = WRAPPERS[rng.below(WRAPPERS.len())];
        let (with, extra) = observation_through(definition, wrapper, rng.percent(25));
        definition = with;
        seeds.extend(extra);
    }
    if !no_head && rng.percent(5) {
        let (with, extra) = stuck_total_branch(definition);
        definition = with;
        seeds.extend(extra);
    }
    (definition, seeds)
}

/// Whether two left-hand sides may have a common instance, read syntactically with every
/// variable a wildcard (an over-approximation of unifiability).
fn compatible(left: &Pat, right: &Pat) -> bool {
    match (left, right) {
        (Pat::As(inner, _, _), other) | (other, Pat::As(inner, _, _)) => compatible(inner, other),
        (Pat::Var(..), _) | (_, Pat::Var(..)) => true,
        (Pat::App(left, left_arguments), Pat::App(right, right_arguments)) => {
            left == right
                && left_arguments
                    .iter()
                    .zip(right_arguments)
                    .all(|(left, right)| compatible(left, right))
        }
        (Pat::Int(left), Pat::Int(right)) => left == right,
        (Pat::Inj(from, to, left), Pat::Inj(other_from, other_to, right)) => {
            from == other_from && to == other_to && compatible(left, right)
        }
        // Lists, and an injection against an application: possibly equal.
        (Pat::List(..), _) | (_, Pat::List(..)) => true,
        (Pat::Inj(..), _) | (_, Pat::Inj(..)) => true,
        (Pat::App(..) | Pat::Int(_), Pat::App(..) | Pat::Int(_)) => false,
    }
}

/// The Bool literal `value`, written as an application the oracle and the KORE text read as
/// the domain value.
pub(super) fn boolean(value: bool) -> Pat {
    // `eqInt(0, 0)` is `true` and `eqInt(0, 1)` is `false` under every reading.
    int_equals(int(0), int(i64::from(!value)))
}

/// A head over lists: `hl([]) = mk(0)`, `hl([X, R..]) = mk(X)`, and either the suffix shape
/// `hl([R.., Y]) = mk(Y)` (an overlap the unifier does not decide) or the longer prefix
/// `hl([X, Y, R..]) = mk(Y)` (an overlap it decides).
pub(super) fn lists(definition: Definition, suffix: bool) -> (Definition, Vec<Pat>) {
    let definition = definition
        .with_lists()
        .head("hl", &["List"], "S")
        .equation(
            app("hl", vec![list(vec![], None, vec![])]),
            app("mk", vec![int(0)]),
        )
        .equation(
            app(
                "hl",
                vec![list(vec![int_var("VarI")], Some("VarR"), vec![])],
            ),
            app("mk", vec![int_var("VarI")]),
        );
    let definition = if suffix {
        definition.equation(
            app(
                "hl",
                vec![list(vec![], Some("VarR"), vec![int_var("VarJ")])],
            ),
            app("mk", vec![int_var("VarJ")]),
        )
    } else {
        definition.equation(
            app(
                "hl",
                vec![list(
                    vec![int_var("VarI"), int_var("VarJ")],
                    Some("VarR"),
                    vec![],
                )],
            ),
            app("mk", vec![int_var("VarI")]),
        )
    };
    let seeds = vec![
        app("hl", vec![list(vec![int(1), int(2)], None, vec![])]),
        app("hl", vec![list(vec![int(3)], None, vec![])]),
    ];
    (definition, seeds)
}

/// An overload family `consE`, `nilE` over `consN`, `nilN` (`N < E`, `Ns < Es`) and a head
/// `len` over it, whose equations overlap modulo the overload axioms; they join when `joining`.
pub(super) fn family(definition: Definition, joining: bool) -> (Definition, Vec<Pat>) {
    let mut definition = definition
        .subsort("N", "E")
        .subsort("Ns", "Es")
        .constructor("n0", &[], "N")
        .constructor("n1", &[], "N")
        .constructor("e0", &[], "E")
        .constructor("nilN", &[], "Ns")
        .constructor("consN", &["N", "Ns"], "Ns")
        .symbol(
            "nilE",
            &[],
            "Es",
            Kind::Head {
                value_production: false,
                total: true,
            },
        )
        .symbol(
            "consE",
            &["E", "Es"],
            "Es",
            Kind::Head {
                value_production: false,
                total: true,
            },
        )
        .overload("consE", "consN")
        .overload("nilE", "nilN")
        .head("len", &["Es"], "S")
        .equation(app("len", vec![cons("nilE")]), app("mk", vec![int(0)]))
        .equation(
            app(
                "len",
                vec![app("consE", vec![var("VarE", "E"), var("VarL", "Es")])],
            ),
            app("mk", vec![int(1)]),
        )
        .equation(
            app(
                "len",
                vec![app(
                    "consE",
                    vec![inj("N", "E", cons("n0")), var("VarL", "Es")],
                )],
            ),
            app("mk", vec![int(if joining { 1 } else { 2 })]),
        );
    for sort in ["N", "E", "Ns", "Es"] {
        definition.sorts.push(sort.into());
    }
    let seeds = vec![
        app(
            "len",
            vec![app("consE", vec![inj("N", "E", cons("n0")), cons("nilE")])],
        ),
        app("len", vec![app("consE", vec![cons("e0"), cons("nilE")])]),
    ];
    (definition, seeds)
}

/// Overloading in a diamond: `sq` over `sqI` and `sqD`, both over `sqE` (`Em < I, D < Ss`), with
/// a head `run` whose equations overlap at the common subsort; they join when `joining`.
pub(super) fn diamond(definition: Definition, joining: bool) -> (Definition, Vec<Pat>) {
    let total_head = Kind::Head {
        value_production: false,
        total: true,
    };
    let mut definition = definition
        .subsort("Em", "I")
        .subsort("Em", "D")
        .subsort("I", "Ss")
        .subsort("D", "Ss")
        .constructor("eI", &[], "I")
        .constructor("eD", &[], "D")
        .constructor("eE", &[], "Em")
        .constructor("sqE", &["Em", "Em"], "Em")
        .symbol("sqI", &["I", "I"], "I", total_head)
        .symbol("sqD", &["D", "D"], "D", total_head)
        .symbol("sq", &["Ss", "Ss"], "Ss", total_head)
        .overload("sq", "sqI")
        .overload("sq", "sqD")
        .overload("sqI", "sqE")
        .overload("sqD", "sqE")
        .head("run", &["Ss"], "S")
        .equation(
            app("run", vec![inj("I", "Ss", var("VarI0", "I"))]),
            app("mk", vec![int(1)]),
        )
        .equation(
            app("run", vec![inj("D", "Ss", var("VarD0", "D"))]),
            app("mk", vec![int(if joining { 1 } else { 2 })]),
        );
    for sort in ["Em", "I", "D", "Ss"] {
        definition.sorts.push(sort.into());
    }
    let seeds = vec![
        app("run", vec![inj("Em", "Ss", cons("eE"))]),
        app(
            "run",
            vec![app(
                "sq",
                vec![inj("Em", "Ss", cons("eE")), inj("Em", "Ss", cons("eE"))],
            )],
        ),
    ];
    (definition, seeds)
}

/// An inner position at a greater overload production whose lesser production has an equation:
/// `go` over `lo` (`Lo < Gr`), `lo(1) = lo(2)`, and `use(go(I)) = mk(I)` (`mk(1)` when
/// `joining`). The subject `use(inj(lo(1)))` matches `use`'s left-hand side only modulo the
/// overload axioms, and `lo(1)` rewrites at the position `go(I)`: an inner pair whose second
/// equation has a sort below the position's (review 2 of the check, F3). It gives `mk(1)` and,
/// after `lo(1) = lo(2)`, `mk(2)` unless `joining`.
pub(super) fn injected_inner(definition: Definition, joining: bool) -> (Definition, Vec<Pat>) {
    let mut definition = definition
        .subsort("Lo", "Gr")
        .head("lo", &["Int"], "Lo")
        .total_head("go", &["Int"], "Gr")
        .overload("go", "lo")
        .head("use", &["Gr"], "S")
        .equation(app("lo", vec![int(1)]), app("lo", vec![int(2)]))
        .equation(
            app("use", vec![app("go", vec![int_var("VarI")])]),
            app("mk", vec![if joining { int(1) } else { int_var("VarI") }]),
        );
    for sort in ["Lo", "Gr"] {
        definition.sorts.push(sort.into());
    }
    let seeds = vec![
        app("use", vec![app("go", vec![int(1)])]),
        app("use", vec![app("go", vec![int(2)])]),
        app("lo", vec![int(1)]),
    ];
    (definition, seeds)
}

/// A family that is not confluent: `g2 : Tt -> Hh` over `l1 : Aa -> Hh` and `l2 : Bb -> Hh`, with
/// `Cc < Aa, Bb < Tt` and no lesser production below both, so `g2(inj(c0))` lowers to two
/// different normal forms.
pub(super) fn non_confluent_family(definition: Definition) -> (Definition, Vec<Pat>) {
    let mut definition = definition
        .subsort("Cc", "Aa")
        .subsort("Cc", "Bb")
        .subsort("Aa", "Tt")
        .subsort("Bb", "Tt")
        .constructor("c0", &[], "Cc")
        .constructor("a0", &[], "Aa")
        .constructor("l1", &["Aa"], "Hh")
        .constructor("l2", &["Bb"], "Hh")
        .symbol(
            "g2",
            &["Tt"],
            "Hh",
            Kind::Head {
                value_production: false,
                total: true,
            },
        )
        .overload("g2", "l1")
        .overload("g2", "l2")
        .head("use", &["Hh"], "S")
        .equation(
            app("use", vec![app("g2", vec![var("VarT", "Tt")])]),
            app("mk", vec![int(0)]),
        )
        .equation(
            app("use", vec![app("l1", vec![var("VarA", "Aa")])]),
            app("mk", vec![int(1)]),
        );
    for sort in ["Cc", "Aa", "Bb", "Tt", "Hh"] {
        definition.sorts.push(sort.into());
    }
    let seeds = vec![
        app("use", vec![app("g2", vec![inj("Cc", "Tt", cons("c0"))])]),
        app("use", vec![app("l1", vec![cons("a0")])]),
    ];
    (definition, seeds)
}

/// Functions over a sort `Z` no equation head's applications reach, whose pair does not join:
/// the pair withdraws no claim.
pub(super) fn irrelevant_cluster(definition: Definition) -> (Definition, Vec<Pat>) {
    let mut definition = definition
        .constructor("z0", &[], "Z")
        .constructor("zs", &["Z"], "Z")
        .function("zf", &["Z"], "Z")
        .equation(app("zf", vec![cons("z0")]), cons("z0"))
        .equation(
            app("zf", vec![var("VarQ", "Z")]),
            app("zs", vec![var("VarQ", "Z")]),
        );
    definition.sorts.push("Z".into());
    let seeds = vec![app("zf", vec![cons("z0")])];
    (definition, seeds)
}

/// The shape of CS C1: `wE(Z) = pE(1)` erases its argument, `gE(5, Y) = wE(Y /Int 0)` and
/// `gE(X, Y) = pE(1)` overlap at `gE(5, Y)`.
pub(super) fn erasing(definition: Definition) -> (Definition, Vec<Pat>) {
    let definition = definition
        .head("wE", &["Int"], "A")
        .head("pE", &["Int"], "A")
        .head("gE", &["Int", "Int"], "A")
        .equation(app("wE", vec![int_var("VarZ")]), app("pE", vec![int(1)]))
        .equation(
            app("gE", vec![int(5), int_var("VarY")]),
            app("wE", vec![div(int_var("VarY"), int(0))]),
        )
        .equation(
            app("gE", vec![int_var("VarX"), int_var("VarY")]),
            app("pE", vec![int(1)]),
        );
    let seeds = vec![
        app("gE", vec![int(5), int(1)]),
        app("pE", vec![int(1)]),
        app("wE", vec![int(2)]),
    ];
    (definition, seeds)
}

/// N1: `gO(X:V) = mk(1)` beside `gO(X:V) = mk(2)` (when `clash`) over a sort `V` whose elements
/// are `v(I)` applications of an equation head: the pair observes `v` through its variable.
pub(super) fn observation(definition: Definition, clash: bool) -> (Definition, Vec<Pat>) {
    let mut definition = definition
        .head("v", &["Int"], "V")
        .head("gO", &["V"], "S")
        .equation(app("gO", vec![var("VarV", "V")]), app("mk", vec![int(1)]));
    if clash {
        definition =
            definition.equation(app("gO", vec![var("VarV", "V")]), app("mk", vec![int(2)]));
    }
    definition.sorts.push("V".into());
    let seeds = vec![
        app("gO", vec![app("v", vec![int(1)])]),
        app("v", vec![int(1)]),
    ];
    (definition, seeds)
}

/// A sort `W` inhabited only by applications of declared total functions without equations,
/// which are normal forms (the design's 3.13 (k)): `tw : Int -> W` and `tw2 : Y -> W`, with `Y`
/// inhabited by an equation head `hW`. The head `gW` over `W` has two equations whose sides
/// differ on every instance: the pair has instances (`W` is inhabited), and its variable does
/// not observe `hW` through the non-injective `tw2`, because `W` has a value in every model
/// (`tw(0)`), which the model of the closure reads `tw2`'s applications to new values as (the
/// design's "Revision after review 1", R1.3).
pub(super) fn through_total_function(definition: Definition) -> (Definition, Vec<Pat>) {
    let mut definition = definition
        .total_function("tw", &["Int"], "W")
        .total_function("tw2", &["Y"], "W")
        .head("hW", &["Int"], "Y")
        .head("gW", &["W"], "S")
        .equation(app("gW", vec![var("VarW", "W")]), app("mk", vec![int(1)]))
        .equation(app("gW", vec![var("VarW", "W")]), app("mk", vec![int(2)]));
    definition.sorts.push("W".into());
    definition.sorts.push("Y".into());
    let seeds = vec![
        app("gW", vec![app("tw", vec![int(1)])]),
        app("gW", vec![app("tw2", vec![app("hW", vec![int(1)])])]),
        app("hW", vec![int(1)]),
    ];
    (definition, seeds)
}

/// How the elements of the observed sort are built from the value production's sort in
/// [`observation_through`].
#[derive(Clone, Copy, Debug)]
pub(super) enum Wrapper {
    TotalFunction,
    Functional,
    Constructor,
    Subsort,
}

pub(super) const WRAPPERS: [Wrapper; 4] = [
    Wrapper::TotalFunction,
    Wrapper::Functional,
    Wrapper::Constructor,
    Wrapper::Subsort,
];

/// N1 through a wrapper (review 1 of the check, F1): `gN(X:On) = mk(1)` and `gN(X:On) = mk(2)`,
/// the elements of `On` built from `Vn` by `wrapper`, and `Vn` built only by the value
/// production `vn`. Every model makes `On`, hence `Vn`, empty, so `vn(1)` is undefined. With
/// `inhabited`, `On` also has a constant constructor `on0`: then the definition has no model.
pub(super) fn observation_through(
    definition: Definition,
    wrapper: Wrapper,
    inhabited: bool,
) -> (Definition, Vec<Pat>) {
    let mut definition = definition.head("vn", &["Int"], "Vn").symbol(
        "gN",
        &["On"],
        "S",
        Kind::Head {
            value_production: false,
            total: false,
        },
    );
    let wrapped = |inner: Pat| match wrapper {
        Wrapper::Subsort => inj("Vn", "On", inner),
        Wrapper::TotalFunction | Wrapper::Functional | Wrapper::Constructor => {
            app("uw", vec![inner])
        }
    };
    definition = match wrapper {
        Wrapper::TotalFunction => definition.total_function("uw", &["Vn"], "On"),
        Wrapper::Functional => definition.functional("uw", &["Vn"], "On"),
        Wrapper::Constructor => definition.constructor("uw", &["Vn"], "On"),
        Wrapper::Subsort => definition.subsort("Vn", "On"),
    };
    if inhabited {
        definition = definition.constructor("on0", &[], "On");
    }
    definition = definition
        .equation(app("gN", vec![var("VarO", "On")]), app("mk", vec![int(1)]))
        .equation(app("gN", vec![var("VarO", "On")]), app("mk", vec![int(2)]));
    definition.sorts.push("On".into());
    definition.sorts.push("Vn".into());
    let mut seeds = vec![
        app("gN", vec![wrapped(app("vn", vec![int(1)]))]),
        app("vn", vec![int(1)]),
    ];
    if inhabited {
        seeds.push(app("gN", vec![cons("on0")]));
    }
    (definition, seeds)
}

/// Review 1 of the check, F2: `ft(Y) = ht(gt(Y), Y)` and `ft(Y) = vt(Y)` with
/// `gt(twt(I)) = mk(1 /Int 0)`, `twt` total and without equations. At `Y = twt(1)` the first
/// side is undefined, so every model makes `vt(twt(1))` undefined.
pub(super) fn stuck_total_branch(definition: Definition) -> (Definition, Vec<Pat>) {
    let plain = Kind::Head {
        value_production: false,
        total: false,
    };
    let mut definition = definition
        .total_function("twt", &["Int"], "Wt")
        .symbol("gt", &["Wt"], "S", plain)
        .symbol("ht", &["S", "Wt"], "S", plain)
        .symbol("ft", &["Wt"], "S", plain)
        .head("vt", &["Wt"], "S")
        .equation(
            app("gt", vec![app("twt", vec![int_var("VarI")])]),
            undefined(),
        )
        .equation(
            app("ht", vec![var("VarZ", "S"), var("VarW", "Wt")]),
            app("vt", vec![var("VarW", "Wt")]),
        )
        .equation(
            app("ft", vec![var("VarW", "Wt")]),
            app(
                "ht",
                vec![app("gt", vec![var("VarW", "Wt")]), var("VarW", "Wt")],
            ),
        )
        .equation(
            app("ft", vec![var("VarW", "Wt")]),
            app("vt", vec![var("VarW", "Wt")]),
        );
    definition.sorts.push("Wt".into());
    let seeds = vec![
        app("ft", vec![app("twt", vec![int(1)])]),
        app("vt", vec![app("twt", vec![int(1)])]),
    ];
    (definition, seeds)
}

/// One fixed definition per feature class, so that every class is present in every run.
#[allow(clippy::too_many_lines, reason = "one template per feature class")]
pub(super) fn templates() -> Vec<(String, Definition, Vec<Pat>)> {
    let base = || {
        Definition::new(&["A"])
            .constructor("c", &[], "A")
            .constructor("d", &[], "A")
            .constructor("k", &["A"], "A")
            .constructor("m", &["Int"], "A")
            .head("f", &["A"], "A")
    };
    let mut templates = Vec::new();
    // A conditional pair refuted by its conditions, and one that is not.
    for refuted in [true, false] {
        let definition = base()
            .conditional(
                app("f", vec![app("m", vec![int_var("VarI")])]),
                cons("c"),
                Some(int_equals(int_var("VarI"), int(0))),
            )
            .conditional(
                app("f", vec![app("m", vec![int_var("VarI")])]),
                cons("d"),
                Some(if refuted {
                    app("notBool", vec![int_equals(int_var("VarI"), int(0))])
                } else {
                    app("ltInt", vec![int_var("VarI"), int(1)])
                }),
            );
        templates.push((
            format!("template conditional (refuted {refuted})"),
            definition,
            vec![
                app("f", vec![app("m", vec![int(0)])]),
                app("f", vec![app("m", vec![int(2)])]),
            ],
        ));
    }
    // Different `ensures` (R9).
    templates.push((
        "template ensures".into(),
        base()
            .full(
                app("f", vec![app("k", vec![cons("c")])]),
                cons("c"),
                None,
                Some(int_equals(int(1), int(1))),
                super::language::DEFAULT_PRIORITY,
            )
            .full(
                app("f", vec![app("k", vec![cons("c")])]),
                cons("c"),
                None,
                Some(int_equals(int(1), int(2))),
                super::language::DEFAULT_PRIORITY,
            ),
        vec![app("f", vec![app("k", vec![cons("c")])])],
    ));
    for suffix in [false, true] {
        let (definition, seeds) = lists(base(), suffix);
        templates.push((
            format!("template lists (suffix {suffix})"),
            definition,
            seeds,
        ));
    }
    // Priorities: CS M1 and CV M3.
    templates.push((
        "template priority (CS M1)".into(),
        Definition::new(&["A"])
            .constructor("a", &[], "A")
            .constructor("cc", &[], "A")
            .constructor("dd", &[], "A")
            .head("b", &[], "A")
            .head("f", &["A"], "A")
            .equation(cons("b"), cons("a"))
            .full(app("f", vec![cons("a")]), cons("cc"), None, None, 40)
            .full(app("f", vec![var("VarX", "A")]), cons("dd"), None, None, 50),
        vec![app("f", vec![cons("b")])],
    ));
    templates.push((
        "template owise (CV M3)".into(),
        Definition::new(&["A"])
            .constructor("a", &[], "A")
            .constructor("cc", &[], "A")
            .constructor("dd", &[], "A")
            .head("g", &[], "A")
            .head("f", &["A"], "A")
            .equation(cons("g"), cons("a"))
            .full(app("f", vec![cons("a")]), cons("cc"), None, None, 10)
            .full(
                app("f", vec![var("VarX", "A")]),
                cons("dd"),
                None,
                None,
                OWISE_PRIORITY,
            ),
        vec![app("f", vec![cons("g")])],
    ));
    for joining in [true, false] {
        let (definition, seeds) = family(base(), joining);
        templates.push((
            format!("template family (joining {joining})"),
            definition,
            seeds,
        ));
        let (definition, seeds) = diamond(base(), joining);
        templates.push((
            format!("template diamond (joining {joining})"),
            definition,
            seeds,
        ));
    }
    for joining in [true, false] {
        let (definition, seeds) = injected_inner(base(), joining);
        templates.push((
            format!("template injected inner (joining {joining})"),
            definition,
            seeds,
        ));
    }
    let (definition, seeds) = non_confluent_family(base());
    templates.push(("template non-confluent family".into(), definition, seeds));
    // A T1 chain: `h(3) = h(1)` below `w`.
    templates.push((
        "template chain".into(),
        Definition::new(&["H"])
            .head("h", &["Int"], "H")
            .head("w", &["H"], "S")
            .equation(app("h", vec![int(3)]), app("h", vec![int(1)]))
            .equation(app("w", vec![app("h", vec![int(3)])]), undefined())
            .head("free", &["Int"], "S"),
        vec![
            app("w", vec![app("h", vec![int(1)])]),
            app("free", vec![int(1)]),
        ],
    ));
    for clash in [true, false] {
        let (definition, seeds) = observation(base(), clash);
        templates.push((
            format!("template observation (clash {clash})"),
            definition,
            seeds,
        ));
    }
    let (definition, seeds) = erasing(base());
    templates.push(("template erasing".into(), definition, seeds));
    // T1: the pair of `h` alone does not mention `w`, whose equation observes `h` in its
    // left-hand side; its inner pairs with the `h` equations join.
    templates.push((
        "template T1 chain".into(),
        Definition::new(&["H"])
            .constructor("c1", &[], "H")
            .constructor("c2", &[], "H")
            .head("h", &["Int"], "H")
            .head("w", &["H"], "S")
            .equation(app("h", vec![int(3)]), cons("c1"))
            .equation(app("h", vec![int(3)]), cons("c2"))
            .equation(
                app("w", vec![app("h", vec![int_var("VarI")])]),
                app("mk", vec![int(1)]),
            )
            .equation(app("w", vec![cons("c1")]), app("mk", vec![int(1)]))
            .equation(app("w", vec![cons("c2")]), app("mk", vec![int(1)])),
        vec![
            app("w", vec![app("h", vec![int(3)])]),
            app("w", vec![app("h", vec![int(1)])]),
        ],
    ));
    // A higher group the join cannot refute: `f(m(I)) = c requires I ==Int 1` above
    // `f(X) = d`, and the pair of `g` whose sides are `f(m(I))` and `d`.
    templates.push((
        "template priority guard".into(),
        base()
            .head("g", &["A"], "A")
            .full(
                app("f", vec![app("m", vec![int_var("VarI")])]),
                cons("c"),
                Some(int_equals(int_var("VarI"), int(1))),
                None,
                40,
            )
            .full(app("f", vec![var("VarX", "A")]), cons("d"), None, None, 50)
            .equation(
                app("g", vec![app("m", vec![int_var("VarI")])]),
                app("f", vec![app("m", vec![int_var("VarI")])]),
            )
            .equation(app("g", vec![app("m", vec![int_var("VarI")])]), cons("d")),
        vec![
            app("g", vec![app("m", vec![int(1)])]),
            app("g", vec![app("m", vec![int(2)])]),
        ],
    ));
    // A `symbolic` equation is no step on ground terms: the root pair of `g` joins only through
    // it, so it does not join.
    templates.push((
        "template symbolic".into(),
        base()
            .constructor("e", &[], "A")
            .head("h", &["A"], "A")
            .head("g", &["A"], "A")
            .equation(app("h", vec![var("VarX", "A")]), cons("e"))
            .symbolic()
            .equation(app("g", vec![cons("c")]), app("h", vec![cons("c")]))
            .equation(app("g", vec![var("VarX", "A")]), cons("e")),
        vec![app("g", vec![cons("c")]), app("h", vec![cons("c")])],
    ));
    let (definition, seeds) = irrelevant_cluster(base());
    templates.push(("template irrelevant cluster".into(), definition, seeds));
    let (definition, seeds) = through_total_function(base());
    templates.push(("template total-function sort".into(), definition, seeds));
    for wrapper in WRAPPERS {
        for inhabited in [false, true] {
            let (definition, seeds) = observation_through(base(), wrapper, inhabited);
            templates.push((
                format!("template observation through {wrapper:?} (inhabited {inhabited})"),
                definition,
                seeds,
            ));
        }
    }
    let (definition, seeds) = stuck_total_branch(base());
    templates.push(("template stuck total branch".into(), definition, seeds));
    // No equation head: functions and lists only.
    templates.push((
        "template no head".into(),
        Definition::new(&["A"])
            .with_lists()
            .constructor("c", &[], "A")
            .constructor("k", &["A"], "A")
            .function("pf", &["A"], "A")
            .equation(app("pf", vec![cons("c")]), app("k", vec![cons("c")]))
            .function("first", &["List"], "Int")
            .equation(
                app(
                    "first",
                    vec![list(vec![int_var("VarI")], Some("VarR"), vec![])],
                ),
                int_var("VarI"),
            ),
        vec![
            app("pf", vec![app("k", vec![cons("c")])]),
            app("first", vec![list(vec![int(1), int(2)], None, vec![])]),
            app("k", vec![cons("c")]),
        ],
    ));
    templates
}
