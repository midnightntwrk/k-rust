// KINK-CENSUS-RUNLIST (fz26 P7-SIMPLE-KINK): #getc(0) in a left-hand-side map key whose match
// fails. No rule applies, yet the run lists IO.getc on unsupportedHooks, so the run is excluded
// by its list rather than the definition by the census.
module LHSIO-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Pgm ::= go(Int)
endmodule

module LHSIO
  imports LHSIO-SYNTAX
  imports DOMAINS
  imports K-IO
  configuration <k> $PGM:Pgm </k> <m> 5 |-> 7 </m> <r> 0 </r>
  rule <k> go(I:Int) => .K ... </k> <m> (I +Int {#getc(0)}:>Int) |-> V:Int ... </m> <r> _ => V </r>
endmodule
