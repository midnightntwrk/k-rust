// An overload placed across `K` (FZ-DATAEND review B1): `f(K)` and `f(Exp)` are both
// `overload(f)`, which gives the overload equation `f_K(kseq(inj{Exp,KItem}(X), dotk)) =
// f_Exp(X)`, not of the canonical shape (`ValueClaimPrecondition`). This baseline stores
// `f(bar ~> .K)`, irreducible here; `kp-m.k` only adds `Exp ::= Bar`, where the same term lowers
// to `f_Exp(inj{Bar,Exp}(bar))`. The two ends are one value of the mutant, so no case is a kill.

module KP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Exp ::= Int
  syntax Bar ::= "bar"
  syntax Foo ::= f(K)   [overload(f)]
  syntax Foo ::= f(Exp) [overload(f)]
  syntax Pgm ::= go(Int)
endmodule
module KP
  imports KP-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => f(bar ~> .K) </s>
endmodule
