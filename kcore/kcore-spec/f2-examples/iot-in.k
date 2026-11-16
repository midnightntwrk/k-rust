// As iot.k, with a rule reading the input cell, for which kompile instantiates STDIN-STREAM's
// unblocking rule.
module IOT-IN-SYNTAX
  imports INT-SYNTAX
endmodule

module IOT-IN
  imports IOT-IN-SYNTAX
  imports INT
  imports LIST
  configuration <k> $PGM:Int </k> <in stream="stdin"> .List </in> <out stream="stdout"> .List </out>
  rule <k> 0 => I ... </k> <in> ListItem(I:Int) => .List ... </in>
endmodule
