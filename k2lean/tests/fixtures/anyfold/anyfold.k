// A kind 1 invariant written with `orBool` list folds (k2lean/docs/invariants.md; the gate's library
// `anyfold`). `hasNeg(L)` and `hasZero(L)` fold the `<log>` list with `orBool`: `false` on `.List`,
// and on `ListItem(X) L` the test of `X` or the fold of the rest, so each is `true` exactly when some
// element passes its test. `k2lean gen --invariant ok` turns each into its value form,
// `Invariant.hasNeg_eq : hasNeg l = some (decide (ElemsSome (fun x => isNeg x = true) l))`, which
// reads both ways: `notBool hasNeg(L)` (no element is negative, an `ElemsOn` fact) and `hasZero(L)`
// (some element is zero, an `ElemsSome` fact). `log` appends a value that is not negative, `start`
// sets `<started>` and prepends a zero, which every later rule keeps: `log` appends after it, and
// `drop` (which removes the first element) applies only before `start`.
requires "domains.md"

module ANYFOLD-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= log(Int)           // append I to the log, when it is not negative
               | start()            // prepend 0 and set the flag
               | drop()             // drop the first element, before start only
               | seq(Cmd, Cmd)
endmodule

module ANYFOLD
  imports ANYFOLD-SYNTAX
  imports INT
  imports LIST
  imports BOOL

  configuration
    <k> $PGM:Cmd </k>
    <log> .List </log>
    <started> false </started>

  syntax Bool ::= ok(GeneratedTopCell) [function, total]
                | hasNeg(List) [function, total]
                | hasZero(List) [function, total]
                | isNeg(KItem) [function, total]
                | isZero(KItem) [function, total]
  rule ok(<generatedTop> <k> _ </k> <log> L </log> <started> B </started> _ </generatedTop>)
    => notBool hasNeg(L) andBool (B impliesBool hasZero(L))
  rule hasNeg(.List) => false
  rule hasNeg(ListItem(X) L) => isNeg(X) orBool hasNeg(L)
  rule hasZero(.List) => false
  rule hasZero(ListItem(X) L) => hasZero(L) orBool isZero(X)
  rule isNeg(I:Int) => I <Int 0
  rule isNeg(_) => false [owise]
  rule isZero(I:Int) => I ==Int 0
  rule isZero(_) => false [owise]

  rule <k> seq(C1, C2) => C1 ~> C2 ... </k> [label(seq)]
  rule <k> log(I) => .K ... </k> <log> L => L ListItem(I) </log> requires I >=Int 0 [label(log)]
  rule <k> start() => .K ... </k> <log> L => ListItem(0) L </log> <started> _ => true </started>
    [label(start)]
  rule <k> drop() => .K ... </k> <log> ListItem(_) L => L </log> <started> false </started>
    [label(drop)]
endmodule
