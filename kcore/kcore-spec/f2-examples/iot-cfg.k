// As iot.k, with a rule applying K-REFLECTION's `#configuration`.
module IOT-CFG-SYNTAX
  imports INT-SYNTAX
endmodule

module IOT-CFG
  imports IOT-CFG-SYNTAX
  imports INT
  imports LIST
  imports K-REFLECTION
  configuration <k> $PGM:Int </k> <in stream="stdin"> .List </in> <out stream="stdout"> .List </out>
  rule <k> 0 => #configuration ... </k>
endmodule
