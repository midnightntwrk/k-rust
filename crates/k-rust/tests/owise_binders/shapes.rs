//! The shapes of the owise cross product (`owise_binders.rs`): five axes of the names a
//! quantifier of a competitor binds, the realizable combinations, and the K text of each.
//! Shared by `owise_binders.rs` and the alpha-invariance harness (`alpha_invariance.rs`),
//! which includes it with `#[path]`.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Binder {
    Named,
    Anonymous,
    Nested,
    Shadowing,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Position {
    Argument,
    Condition,
}

/// How the probed competitor's bound names meet a set of names of the axiom.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Relation {
    Absent,
    SameSort,
    OtherSort,
}

pub const RELATIONS: [Relation; 3] = [Relation::Absent, Relation::SameSort, Relation::OtherSort];

#[derive(Clone, Copy, Debug)]
pub struct Shape {
    pub binder: Binder,
    pub position: Position,
    pub owise: Relation,
    pub other: Relation,
    pub minted: Relation,
}

impl Shape {
    pub fn name(&self) -> String {
        format!(
            "{:?}-{:?}/owise-{:?}/other-{:?}/minted-{:?}",
            self.binder, self.position, self.owise, self.other, self.minted
        )
    }

    /// Whether a name of `q`'s binders is already held when `q` is emitted, so that it must be
    /// renamed.
    pub fn q_taken(&self) -> bool {
        self.owise != Relation::Absent
            || self.other != Relation::Absent
            || self.minted != Relation::Absent
    }
}

/// Why no K text realizes the shape, or `None` when one does.
pub fn unrealizable(shape: &Shape) -> Option<&'static str> {
    if shape.minted != Relation::Absent && shape.binder != Binder::Anonymous {
        // A named binder spelled `_Gen<N>` is read as anonymous (FU-26), so only an anonymous
        // binder's variables are spelled like a minted name.
        return Some(
            "a minted name is spelled `_Gen<N>`, as only an anonymous binder's variables are",
        );
    }
    if shape.minted != Relation::Absent && shape.owise != Relation::Absent {
        // Every name of the owise rule is in use before the first name is minted.
        return Some("no minted name equals a name of the owise rule");
    }
    None
}

/// Every shape of the cross product, with the reason it is dropped where it is.
pub fn cross_product() -> Vec<(Shape, Option<&'static str>)> {
    let mut shapes = Vec::new();
    for binder in [
        Binder::Named,
        Binder::Anonymous,
        Binder::Nested,
        Binder::Shadowing,
    ] {
        for position in [Position::Argument, Position::Condition] {
            for owise in RELATIONS {
                for other in RELATIONS {
                    for minted in RELATIONS {
                        let shape = Shape {
                            binder,
                            position,
                            owise,
                            other,
                            minted,
                        };
                        shapes.push((shape, unrealizable(&shape)));
                    }
                }
            }
        }
    }
    shapes
}

pub const HEADER: &str = "module P-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module P
  imports P-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= done(Int) [symbol(done)]
  syntax Pair ::= g(Int, Int) [symbol(g)]
  syntax Int ::= f(Pair, Bool) [function, symbol(f)]
  rule [go]: <k> go(N) => done(f(g(N, 0), true)) ... </k>
";

/// The K text of a shape: the competitors `m` (a quantifier-free competitor whose free variables
/// are minted first), `p` (another competitor binding names) and `q` (the probed one), in this
/// rule order, and the owise rule `o`. `m` and `p` never apply at the programs run.
pub fn source(shape: &Shape) -> String {
    let anonymous = shape.binder == Binder::Anonymous;
    let mut rules = String::new();
    // `m`'s free variables are minted in order: `_Gen0`, `_Gen1` (Int, or Bool), ...
    match shape.minted {
        Relation::Absent => {}
        Relation::SameSort => rules
            .push_str("  rule [m]: f(g(A:Int, D:Int), C:Bool) => 3 requires C andBool notBool C\n"),
        Relation::OtherSort => {
            rules.push_str("  rule [m]: f(P:Pair, C:Bool) => 3 requires C andBool notBool C\n")
        }
    }
    // `q`'s bound names are `Y` (and `Y0` when nested) at Int; an anonymous binder's bound
    // variable is the body's `_`, which the frontend names `_Gen1` (the binder itself is `_Gen0`).
    let p = match (anonymous, shape.other) {
        (_, Relation::Absent) => None,
        (false, Relation::SameSort) => {
            Some("#Exists Y:Int . #Exists Y0:Int . ({U #Equals 1000} #And {Y #Equals Y0})")
        }
        (false, Relation::OtherSort) => {
            Some("#Exists Y:Bool . #Exists Y0:Bool . ({U #Equals 1000} #And {Y #Equals Y0})")
        }
        (true, Relation::SameSort) => {
            Some("#Exists _:Int . ({U #Equals 1000} #And {_:Int #Equals V})")
        }
        (true, Relation::OtherSort) => {
            Some("#Exists _:Bool . ({U #Equals 1000} #And {_:Bool #Equals C})")
        }
    };
    if let Some(condition) = p {
        rules.push_str(&format!(
            "  rule [p]: f(g(U:Int, V:Int), C:Bool) => 2 requires {condition}\n"
        ));
    }
    let q = match (shape.binder, shape.position) {
        (Binder::Named, Position::Argument) => {
            "f(#Exists Y:Int . g(Y, Z:Int), B:Bool) => 1".to_owned()
        }
        (Binder::Anonymous, Position::Argument) => {
            "f(#Exists _:Int . g(_, Z:Int), B:Bool) => 1".to_owned()
        }
        (Binder::Nested, Position::Argument) => {
            "f(#Exists Y:Int . #Exists Y0:Int . g(Y, Y0), B:Bool) => 1".to_owned()
        }
        (Binder::Shadowing, Position::Argument) => {
            "f(#Exists Y:Int . g(Y, #Exists Y:Int . Y), B:Bool) => 1".to_owned()
        }
        (binder, Position::Condition) => {
            let condition = match binder {
                Binder::Named => "#Exists Y:Int . ({X #Equals Y} #And {true #Equals Y <Int 3})",
                Binder::Anonymous => "#Exists _:Int . {X #Equals _ *Int 2}",
                Binder::Nested => {
                    "#Exists Y:Int . #Exists Y0:Int . ({X #Equals Y} #And {Y0 #Equals Y} #And {true #Equals Y0 <Int 3})"
                }
                Binder::Shadowing => {
                    "#Exists Y:Int . ({X #Equals Y} #And {true #Equals Y <Int 3} #And (#Exists Y:Int . {Y #Equals 2}))"
                }
            };
            format!("f(g(X:Int, Z:Int), B:Bool) => 1 requires {condition}")
        }
    };
    rules.push_str(&format!("  rule [q]: {q}\n"));
    let owise = match (anonymous, shape.owise) {
        (_, Relation::Absent) => "f(P:Pair, C:Bool)",
        (false, Relation::SameSort) => "f(g(Y:Int, Y0:Int), C:Bool)",
        (false, Relation::OtherSort) => "f(Y:Pair, Y0:Bool)",
        (true, Relation::SameSort) => "f(g(_, _), C:Bool)",
        (true, Relation::OtherSort) => "f(_, _)",
    };
    rules.push_str(&format!("  rule [o]: {owise} => 0 [owise]\n"));
    format!("{HEADER}{rules}endmodule\n")
}

/// The value the owise-defined `f(g(n, 0), true)` has: `q` applies where its condition holds.
pub fn expected_value(shape: &Shape, n: i64) -> i64 {
    let holds = match shape.binder {
        Binder::Anonymous => n % 2 == 0,
        Binder::Named | Binder::Nested | Binder::Shadowing => n < 3,
    };
    i64::from(holds)
}

pub const PROGRAMS: [i64; 3] = [1, 2, 4];
