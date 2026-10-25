// FZ-DATAEND review R3-B1 (pre-existing: main kills it): an unbroken ov.k-style family plus
// p(_:Id, _:Ids) => a and p(_:Exp, _:Exps) => bb, which overlap only modulo the overload axiom
// and so equate a with bb (UnjoinedCriticalPair). This baseline stores a, m.k stores bb: one value
// in both theories, so no case kills.

module MO-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Exp  ::= Int | Id
  syntax Ids  ::= List{Id,","}  [overload(Exps)]
  syntax Exps ::= List{Exp,","} [overload(Exps)]
  syntax Exps ::= Ids
  syntax A    ::= "a"
  syntax B    ::= "bb"
  syntax AB   ::= A | B
  syntax Pgm  ::= go(Int)
endmodule
module MO
  imports MO-SYNTAX
  imports DOMAINS
  syntax AB ::= p(Exps) [function]
  rule p(_I:Id , _Is:Ids) => a
  rule p(_E:Exp , _Es:Exps) => bb
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => a </s>
endmodule
