module E3-VARS-LIST
  imports INT
  imports LIST
  syntax Exp ::= go() [symbol(go)]
  configuration <k> $PGM:Exp </k> <l> .List </l>
  rule <k> go() => .K ... </k> <l> L => ListItem(?V:Int) L </l>
endmodule
