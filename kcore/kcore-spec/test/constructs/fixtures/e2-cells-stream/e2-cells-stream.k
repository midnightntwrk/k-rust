module E2-CELLS-STREAM
  imports INT
  imports LIST
  syntax Exp ::= a() [symbol(a)]
  configuration <t> <k> $PGM:Exp </k> <in stream="stdin"> .List </in> <out stream="stdout"> .List </out> </t>
endmodule
