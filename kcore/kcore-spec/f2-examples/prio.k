// F2 probe: priorities, an [owise] rule, and a diamond of subsorts (D below B and C), with no
// imports (the `none` fixed text), small enough for kcore-spec's kernel check (test/F2Check.lean).
module PRIO
  syntax D ::= "d" [symbol(d)]
  syntax B ::= D | "b" [symbol(b)]
  syntax C ::= D | "c" [symbol(c)]
  syntax KItem ::= go(B) [symbol(go)] | out(C) [symbol(out)] | other(B) [symbol(other)] | stop() [symbol(stop)]
  configuration <k> $PGM:K </k>
  rule <k> go(X:D) => out(X) ... </k> [priority(40)]
  rule <k> go(X:B) => other(X) ... </k>
  rule <k> go(_) => stop() ... </k> [owise]
endmodule
