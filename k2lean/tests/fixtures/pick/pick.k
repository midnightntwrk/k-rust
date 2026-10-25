// Functions with free-key map patterns, none recursive, called by the rules: `relate` proves their
// commutation with a translation that keeps every constructor's position (k2lean/docs/design.md,
// section 3.2) and states the bisimulation (demos/PickRel, the fixture under two namespaces).
requires "domains.md"

module PICK-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "neg" | "two" | "any" | "drop"
endmodule

module PICK
  imports PICK-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  configuration <T>
      <k> $PGM:Pgm </k>
      <m> 1 |-> 2 3 |-> -4 </m>
      <out> 0 </out>
    </T>

  // one free key: some value is negative
  syntax Bool ::= hasNeg(Map) [function, total]
  rule hasNeg((_ |-> V:Int) _) => true requires V <Int 0
  rule hasNeg(_) => false [owise]

  // two free keys: two positive values
  syntax Bool ::= twoPos(Map) [function, total]
  rule twoPos((_ |-> V1:Int) (_ |-> V2:Int) _) => true requires V1 >Int 0 andBool V2 >Int 0
  rule twoPos(_) => false [owise]

  // partial: a positive value (the least key's, in the map's order)
  syntax Int ::= anyPos(Map) [function]
  rule anyPos((_ |-> V:Int) _) => V requires V >Int 0

  rule <k> neg => .K ... </k> <m> M </m> <out> _ => 1 </out> requires hasNeg(M)
  rule <k> two => .K ... </k> <m> M </m> <out> _ => 2 </out> requires twoPos(M)
  rule <k> any => .K ... </k> <m> M </m> <out> _ => anyPos(M) </out>
  // a free-key rule: drop a binding with a negative value
  rule <k> drop ... </k> <m> (_ |-> V:Int => .Map) ... </m> requires V <Int 0
endmodule
