// A mutant of `ov.k` (FZ-DATAEND) whose overload equations differ: it adds `Ints`, a third list of
// the family, so `_,_Exps` gains the equation
// `_,_Exps(inj{Int,Exp}(E), inj{Ints,Exps}(Es)) = inj{Ints,Exps}(_,_Ints(E, Es))`, and its rule
// prepends `0` as `ov-prepend.k`'s does. `h(3)` ends with a list the two definitions name
// differently: `_,_Exps(inj{Int,Exp}(3), ..)` is a normal form of the baseline only. `_,_Exps`
// does not mean the same in both, so no end that holds it is compared, and the case is never a
// kill.

module OV-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Exp  ::= Int | Id
  syntax Ids  ::= List{Id,","}  [overload(Exps)]
  syntax Ints ::= List{Int,","} [overload(Exps)]
  syntax Exps ::= List{Exp,","} [overload(Exps)]
  syntax Exps ::= Ids | Ints
  syntax Pgm  ::= "h" "(" Exps ")"
endmodule

module OV
  imports OV-SYNTAX
  imports DOMAINS

  configuration <k> $PGM:Pgm </k> <s> .K </s>

  rule <k> h(Es) => .K </k> <s> _ => 0, Es </s>
endmodule
