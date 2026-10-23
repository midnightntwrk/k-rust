// A mutant of `ov.k` (FZ-DATAEND) with the same syntax, and so the same overload equations, whose
// rule stores the list with `0` prepended: `h(3)` ends with
// `_,_Exps(inj{Int,Exp}(0), _,_Exps(inj{Int,Exp}(3), inj{Ids,Exps}(.Ids)))` where the baseline
// ends with `_,_Exps(inj{Int,Exp}(3), inj{Ids,Exps}(.Ids))`. Both ends are data, so the anchor
// kills.

module OV-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Exp  ::= Int | Id
  syntax Ids  ::= List{Id,","}  [overload(Exps)]
  syntax Exps ::= List{Exp,","} [overload(Exps)]
  syntax Exps ::= Ids
  syntax Pgm  ::= "h" "(" Exps ")"
endmodule

module OV
  imports OV-SYNTAX
  imports DOMAINS

  configuration <k> $PGM:Pgm </k> <s> .K </s>

  rule <k> h(Es) => .K </k> <s> _ => 0, Es </s>
endmodule
