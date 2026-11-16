module STORE-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= put(Int, Int) [symbol(put)] | get(Int) [symbol(get)] | new() [symbol(new)] | done() [symbol(done)]
endmodule
module STORE
  imports STORE-SYNTAX
  imports INT
  imports MAP
  configuration <T> <k> $PGM:Cmd </k> <state> .Map </state> </T>
  rule [put]: <k> put(K, V) => done() </k> <state> M => M [ K <- V ] </state>
  rule [get]: <k> get(K) => put(K, V +Int 1) </k> <state> K |-> V _ </state>
  rule [new]: <k> new() => put(!I:Int, 0) </k>
endmodule
