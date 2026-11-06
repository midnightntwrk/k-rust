// Flow fixture: the key <id> of the Map cell <thread> declared unobservable. A Map holds each
// instance by its key, which each element also holds as its first argument beside the instance,
// so no projection may leave the key out of the instances.
module COLLECTIONKEY-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "emit" "(" Int ")" [symbol(emit)]
endmodule

module COLLECTIONKEY
  imports COLLECTIONKEY-SYNTAX
  imports INT
  configuration <k> $PGM:Stmt </k> <out> 0 </out>
                <threads> <thread multiplicity="*" type="Map"> <id unobservable=""> 0 </id> <tmp> 0 </tmp> </thread> </threads>

  rule [emit]: <k> emit(I:Int) => .K ... </k> <out> O => O +Int I </out>
endmodule
