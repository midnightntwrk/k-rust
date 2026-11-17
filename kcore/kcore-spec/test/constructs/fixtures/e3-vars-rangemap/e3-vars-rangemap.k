module E3-VARS-RANGEMAP
  imports INT
  imports RANGEMAP
  syntax Exp ::= go() [symbol(go)]
  configuration <k> $PGM:Exp </k> <r> .RangeMap </r>
  rule <k> go() => .K ... </k> <r> _ => [0, 1) r|-> ?V:Int </r>
endmodule
