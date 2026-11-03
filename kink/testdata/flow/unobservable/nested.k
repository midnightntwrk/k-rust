// Flow fixture: unobs.k with <out> and the unobservable <scratch> inside the wrapper cell
// <state>, so a narrowing to <state> still leaves <scratch> out, and by default <state>'s
// observed child <out> is compared, not <state> itself.
module NESTED-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "emit" "(" Int ")" [symbol(emit)]
                | "note" "(" Int ")" [symbol(note)]
                | Stmt ";" Stmt [right, symbol(seq)]
endmodule

module NESTED
  imports NESTED-SYNTAX
  imports INT
  configuration <k> $PGM:Stmt </k> <state> <out> 0 </out> <scratch unobservable=""> 0 </scratch> </state>

  rule [seq]: S1:Stmt ; S2:Stmt => S1 ~> S2
  rule [emit]: <k> emit(I:Int) => .K ... </k> <out> O => O +Int I </out>
  rule [note]: <k> note(I:Int) => .K ... </k> <scratch> _ => I </scratch>
endmodule
