// F2 probe (P1.3, risk R4): hooked symbols of the definition's own module. `ok` and `bad` hook into
// a namespace no registry interprets (`PH`, declared with `--hook-namespaces PH`), so they are
// parameters of the semantics; `both` hooks into `BOOL.and`, so it has `_andBool_`'s meaning.
// Rules 1 and 2 are apart for every interpretation (complementary literals of one term); rule 3
// overlaps both unless the interpretation makes `bad` exclude `ok` and its complement.
module PH
  imports BOOL
  syntax Val ::= "a" [symbol(a)] | "b" [symbol(b)]
  syntax Bool ::= ok(Val) [function, hook(PH.ok), symbol(ok)]
                | bad(Val) [function, hook(PH.bad), symbol(bad)]
                | both(Bool, Bool) [function, hook(BOOL.and), symbol(both)]
  syntax KItem ::= go(Val) [symbol(go)] | yes() [symbol(yes)] | no() [symbol(no)] | oops() [symbol(oops)]
  configuration <k> $PGM:K </k>
  rule <k> go(X) => yes() ... </k> requires ok(X)
  rule <k> go(X) => no() ... </k> requires notBool ok(X)
  rule <k> go(X) => oops() ... </k> requires both(bad(X), true)
endmodule
