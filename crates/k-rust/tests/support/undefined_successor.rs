//! The definition of the matrix of `\bottom` successors (design/undefined-successor.md §4): one
//! program per way a candidate's result is found `\bottom` and per shape of the step around it.
//! `undefined_step_coverage.rs` runs it on every execution and search route, and
//! `proof_semantics.rs` proves its one-path and all-path claims.

#![allow(dead_code)]

/// How a candidate's result is found `\bottom`: the right-hand side of the `\bottom` rule,
/// the right-hand side of a second `\bottom` rule beside it, and the rule's attribute.
pub struct Route {
    pub name: &'static str,
    pub prefix: char,
    rhs: &'static str,
    second: &'static str,
    attribute: &'static str,
    /// Whether the step itself finds the result `\bottom` (it simplifies the right-hand side
    /// of a rule with a partial symbol, a literal `#Bottom`, or any rule with the console).
    pub in_step: bool,
}

/// Declared `preserves-definedness` rules and `total` symbols are not simplified by the step,
/// so their result is decided when their successor is normalized; a partial symbol or a
/// literal `#Bottom` is decided by the step itself.
pub const ROUTES: [Route; 8] = [
    Route {
        name: "undefined builtin, declared",
        prefix: 'b',
        rhs: "val(X /Int 0)",
        second: "w(X /Int 0)",
        attribute: " [preserves-definedness]",
        in_step: false,
    },
    Route {
        name: "#Bottom equation of a partial symbol, declared",
        prefix: 'e',
        rhs: "val(bot(X))",
        second: "w(bot(X))",
        attribute: " [preserves-definedness]",
        in_step: false,
    },
    Route {
        name: "#Bottom equation of a total symbol",
        prefix: 't',
        rhs: "val(tb(X))",
        second: "w(tb(X))",
        attribute: "",
        in_step: false,
    },
    Route {
        name: "refuted equation ensures of a total symbol",
        prefix: 'q',
        rhs: "val(te(X))",
        second: "w(te(X))",
        attribute: "",
        in_step: false,
    },
    Route {
        name: "existential successor: an ensures binds the argument of a total #Bottom equation",
        prefix: 'x',
        rhs: "val(tb(?Y))",
        second: "w(tb(?Y))",
        attribute: " ensures ?Y ==Int X",
        in_step: false,
    },
    Route {
        name: "#Bottom equation found in the step",
        prefix: 'n',
        rhs: "val(bot(X))",
        second: "w(bot(X))",
        attribute: "",
        in_step: true,
    },
    Route {
        name: "literal #Bottom",
        prefix: 'l',
        rhs: "#Bottom",
        second: "#Bottom",
        attribute: "",
        in_step: true,
    },
    Route {
        name: "literal #Bottom, declared",
        prefix: 'd',
        rhs: "#Bottom",
        second: "#Bottom",
        attribute: " [preserves-definedness]",
        in_step: true,
    },
];

/// The step around the `\bottom` rule `<p>a`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Shape {
    /// `<p>b`, of the same priority, rewrites every instance to `done`.
    Covering,
    /// `<p>b` rewrites every instance to `done` at a lower priority.
    Lower,
    /// No other rule.
    Alone,
    /// `<p>b`, of the same priority, is `\bottom` too.
    Two,
}

pub const SHAPES: [(Shape, char); 4] = [
    (Shape::Covering, 'c'),
    (Shape::Lower, 'p'),
    (Shape::Alone, 'o'),
    (Shape::Two, 'w'),
];

/// Every program of the matrix, with its route and shape.
pub fn programs() -> Vec<(String, &'static Route, Shape)> {
    ROUTES
        .iter()
        .flat_map(|route| {
            SHAPES
                .iter()
                .map(move |&(shape, letter)| (format!("{}{letter}", route.prefix), route, shape))
        })
        .collect()
}

/// The matrix definition: one program per route and shape, over the functions `bot`
/// (partial, `#Bottom` on 0), `tb` (`total`, `#Bottom` on 0) and `te` (`total`, whose
/// equation's `ensures` fails on 0).
pub fn matrix_source() -> String {
    let mut syntax = String::new();
    let mut rules = String::new();
    for (program, route, shape) in programs() {
        syntax.push_str(&format!(
            "                | {program}(Int) [symbol({program})]\n"
        ));
        let variable = |rhs: &str| {
            if rhs.contains('X') || route.attribute.contains('X') {
                "X"
            } else {
                "_"
            }
        };
        rules.push_str(&format!(
            "  rule [{program}a]: <k> {program}({}) => {} </k>{}\n",
            variable(route.rhs),
            route.rhs,
            route.attribute
        ));
        match shape {
            Shape::Covering => {
                rules.push_str(&format!(
                    "  rule [{program}b]: <k> {program}(_) => done </k>\n"
                ));
            }
            Shape::Lower => rules.push_str(&format!(
                "  rule [{program}b]: <k> {program}(_) => done </k> [priority(60)]\n"
            )),
            Shape::Alone => {}
            Shape::Two => rules.push_str(&format!(
                "  rule [{program}b]: <k> {program}({}) => {} </k>{}\n",
                variable(route.second),
                route.second,
                route.attribute
            )),
        }
    }
    format!(
        r#"module FU42-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= "done" [symbol(done)]
            | val(Int) [symbol(val)]
            | w(Int) [symbol(w)]
{syntax}  syntax Int ::= bot(Int) [function, symbol(bot)]
           | tb(Int) [function, total, symbol(tb)]
           | te(Int) [function, total, symbol(te)]
endmodule

module FU42
  imports FU42-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>

  rule [boteq]:  bot(I) => #Bottom requires I ==Int 0
  rule [boteq2]: bot(I) => I requires I =/=Int 0
  rule [tbeq]:   tb(I) => #Bottom requires I ==Int 0
  rule [tbeq2]:  tb(I) => I requires I =/=Int 0
  rule [teeq]:   te(I) => 1 ensures I =/=Int 0
{rules}endmodule
"#
    )
}
