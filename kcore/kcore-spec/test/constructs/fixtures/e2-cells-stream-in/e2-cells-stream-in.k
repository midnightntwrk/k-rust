module E2-CELLS-STREAM-IN
  imports INT
  imports LIST
  syntax Exp ::= a() [symbol(a)]
  configuration <t> <k> $PGM:Exp </k> <in stream="stdin"> .List </in> <out stream="stdout"> .List </out> </t>
  rule <k> a() => .K ... </k> <in> ListItem(_:Int) => .List ... </in>
endmodule
