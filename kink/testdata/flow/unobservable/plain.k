// Flow fixture: unobs.k without the unobservable declaration, so every cell is compared.
module UNOBS-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "emit" "(" Int ")" [symbol(emit)]
                | "note" "(" Int ")" [symbol(note)]
                | Stmt ";" Stmt [right, symbol(seq)]
endmodule

module UNOBS
  imports UNOBS-SYNTAX
  imports INT
  configuration <k> $PGM:Stmt </k> <out> 0 </out> <scratch> 0 </scratch>

  rule [seq]: S1:Stmt ; S2:Stmt => S1 ~> S2
  rule [emit]: <k> emit(I:Int) => .K ... </k> <out> O => O +Int I </out>
  rule [note]: <k> note(I:Int) => .K ... </k> <scratch> _ => I </scratch>
endmodule
