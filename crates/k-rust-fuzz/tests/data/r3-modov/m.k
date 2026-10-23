// The mutant of r3-modov/b.k: it stores bb.

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
  rule <k> go(_) => .K </k> <s> _ => bb </s>
endmodule
