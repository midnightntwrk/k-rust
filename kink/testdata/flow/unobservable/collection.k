// Flow fixture: an unobservable cell <tmp> inside the `*` cell <thread>, so its position varies
// between ends and no projection can leave it out alone; the enclosing <threads> can be.
module COLLECTION-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "emit" "(" Int ")" [symbol(emit)]
endmodule

module COLLECTION
  imports COLLECTION-SYNTAX
  imports INT
  configuration <k> $PGM:Stmt </k> <out> 0 </out>
                <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <tmp unobservable=""> 0 </tmp> </thread> </threads>

  rule [emit]: <k> emit(I:Int) => .K ... </k> <out> O => O +Int I </out>
endmodule
