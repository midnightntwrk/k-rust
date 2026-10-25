// A two-level security type system for kimp's IMP (Volpano and Smith), as a separate K definition
// over the same syntax (demos/ImpNI states kimp's noninterference for it). Levels are `lo` and
// `hi`; a labelling maps identifiers to levels. `lev` is the level of an expression (the join of
// its variables'), undefined on an unlabelled variable. `sec` accepts a statement at a low
// program counter: a low variable is assigned only a low expression, and a branch or loop on a
// high condition is confined (`conf`: it assigns only high variables).

requires "imp.k"

module IMP-SEC-SYNTAX
  imports IMP-SYNTAX
endmodule

module IMP-SEC
  imports IMP-SEC-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports K-EQUAL

  syntax Level ::= "lo" | "hi"

  syntax Level ::= join(Level, Level) [function, total]
  rule join(lo, L) => L
  rule join(hi, _) => hi

  syntax Level ::= lev(Expr, Map) [function]
  rule lev(_:Int, _) => lo
  rule lev(_:Bool, _) => lo
  rule lev(X:Id, X |-> L:Level _:Map) => L
  rule lev(- E, G) => lev(E, G)
  rule lev(! E, G) => lev(E, G)
  rule lev(E1 + E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 - E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 * E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 / E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 >= E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 > E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 <= E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 < E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 == E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 != E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 && E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 || E2, G) => join(lev(E1, G), lev(E2, G))

  syntax Bool ::= conf(Stmt, Map) [function, total]
  rule conf({}, _) => true
  rule conf({ S }, G) => conf(S, G)
  rule conf(X:Id = _ ;, G) => lev(X, G) ==K hi
  rule conf(S1:Stmt S2:Stmt, G) => conf(S1, G) andBool conf(S2, G)
  rule conf(if (_) S1 else S2, G) => conf(S1, G) andBool conf(S2, G)
  rule conf(if (_) S, G) => conf(S, G)
  rule conf(while (_) S, G) => conf(S, G)
  rule conf(_, _) => false [owise]

  syntax Bool ::= sec(Stmt, Map) [function, total]
  rule sec({}, _) => true
  rule sec({ S }, G) => sec(S, G)
  rule sec(X:Id = E ;, G) => true requires lev(X, G) ==K hi orBool lev(E, G) ==K lo
  rule sec(S1:Stmt S2:Stmt, G) => sec(S1, G) andBool sec(S2, G)
  rule sec(if (C) S1 else S2, G) => sec(S1, G) andBool sec(S2, G) requires lev(C, G) ==K lo
  rule sec(if (C) S1 else S2, G) => conf(S1, G) andBool conf(S2, G) requires lev(C, G) ==K hi
  rule sec(if (C) S, G) => sec(S, G) requires lev(C, G) ==K lo
  rule sec(if (C) S, G) => conf(S, G) requires lev(C, G) ==K hi
  rule sec(while (C) S, G) => sec(S, G) requires lev(C, G) ==K lo
  rule sec(while (C) S, G) => conf(S, G) requires lev(C, G) ==K hi
  rule sec(_, _) => false [owise]

  // a configuration only so that the definition compiles as a main module
  configuration <k> $PGM:Stmt </k>
endmodule
