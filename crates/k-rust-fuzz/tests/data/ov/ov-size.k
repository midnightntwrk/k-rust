// A mutant of `ov.k` (FZ-DATAEND) whose end holds a genuine function application: it stores
// `size(Es)`, a total function whose one equation applies to a list of identifiers only, so
// `h(3)` ends with the unevaluated `size(_,_Exps(3, .Ids))`. That end is not data: its value is whatever a model makes
// of `size`, which may be the baseline's end. No case kills.

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

  syntax Int ::= size(Exps) [function, total]
  rule size(_:Ids) => 0

  rule [store]: <k> h(Es) => .K </k> <s> _ => size(Es) </s>
endmodule
