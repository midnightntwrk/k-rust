// The mutant of r3-propagate/b.k: it stores bb.

module PR-SYNTAX
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
  syntax A    ::= "a"
  syntax B    ::= "bb"
  syntax AB   ::= A | B
  syntax Pgm  ::= go(Int)
endmodule
module PR
  imports PR-SYNTAX
  imports DOMAINS
  syntax AB ::= pick(Exps) [function]
  rule pick(.Ids) => a
  rule pick(.Vals) => bb
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => bb </s>
endmodule
