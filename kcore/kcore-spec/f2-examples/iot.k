// Stream cells: `<in stream="stdin">` and `<out stream="stdout">` bring K's K-IO, K-REFLECTION and the
// rules of its stream modules into the definition, the rules instantiated on these cells.
module IOT-SYNTAX
  imports INT-SYNTAX
endmodule

module IOT
  imports IOT-SYNTAX
  imports INT
  imports LIST
  configuration <k> $PGM:Int </k> <in stream="stdin"> .List </in> <out stream="stdout"> .List </out>
  rule <k> I:Int => .K ... </k> <out> ... .List => ListItem(I) </out>
endmodule
