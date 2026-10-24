// KINK-CENSUS-RUNLIST (fz26 P7-SIMPLE-KINK review B1): the bytes pair in a left-hand-side map key.
// go("ab") fails the match after evaluating both hooks, so no rule names them; the pair stays in
// the census, so the definition stays excluded.
module LHS-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Pgm ::= go(String)
endmodule

module LHS
  imports LHS-SYNTAX
  imports DOMAINS
  imports BYTES
  configuration <k> $PGM:Pgm </k> <m> "zz" |-> 7 </m> <r> 0 </r>
  rule <k> go(S:String) => .K ... </k> <m> Bytes2String(String2Bytes(S)) |-> V:Int ... </m> <r> _ => V </r>
endmodule
