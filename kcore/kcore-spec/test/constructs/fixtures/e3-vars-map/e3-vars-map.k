module E3-VARS-MAP
  imports INT
  imports MAP
  syntax Exp ::= set(Int) [symbol(set)]
  configuration <k> $PGM:Exp </k> <m> .Map </m>
  rule <k> set(K) => .K ... </k> <m> .Map => K |-> ?V:Int </m>
endmodule
