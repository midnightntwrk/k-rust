// A broken overload family (FZ-DATAEND review B2): `Bot < Id2, Val`, `Ids` and `Vals` both
// `overload(Exps)`, both above the common `Bots`, which is not overloaded. `.Exps` lowers to
// `inj{Ids,Exps}(.Ids)` and to `inj{Vals,Exps}(.Vals)`, a pair the load reports as not joined
// (`UnjoinedCriticalPair`), so the family's axioms equate the two in every model. This baseline
// stores `.Ids`; `dia-m.k` stores `.Vals`. The two ends are constructor terms the family
// identifies, so no case is a kill.

module DIA-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Bot  ::= "b"
  syntax Id2  ::= Bot | "x"
  syntax Val  ::= Bot | Int
  syntax Exp  ::= Id2 | Val
  syntax Bots ::= List{Bot,","}
  syntax Ids  ::= List{Id2,","} [overload(Exps)]
  syntax Vals ::= List{Val,","} [overload(Exps)]
  syntax Exps ::= List{Exp,","} [overload(Exps)]
  syntax Ids  ::= Bots
  syntax Vals ::= Bots
  syntax Exps ::= Ids | Vals
  syntax Pgm  ::= go(Int)
endmodule
module DIA
  imports DIA-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => .Ids </s>
endmodule
