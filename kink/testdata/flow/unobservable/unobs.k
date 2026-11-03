// Flow fixture: the compared cells. `emit(I)` adds I to the observed cell <out>; `note(I)`
// writes I to <scratch>, which the specification declares unobservable, so no comparison reads
// it. plain.k is this definition without the declaration; nested.k holds <out> and <scratch>
// inside a wrapper cell; collection.k holds an unobservable cell inside a `*` cell, whose
// position varies between ends.
module UNOBS-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "emit" "(" Int ")" [symbol(emit)]
                | "note" "(" Int ")" [symbol(note)]
                | Stmt ";" Stmt [right, symbol(seq)]
endmodule

module UNOBS
  imports UNOBS-SYNTAX
  imports INT
  configuration <k> $PGM:Stmt </k> <out> 0 </out> <scratch unobservable=""> 0 </scratch>

  rule [seq]: S1:Stmt ; S2:Stmt => S1 ~> S2
  rule [emit]: <k> emit(I:Int) => .K ... </k> <out> O => O +Int I </out>
  rule [note]: <k> note(I:Int) => .K ... </k> <scratch> _ => I </scratch>
endmodule
