module BOUNDED-SEARCH
  syntax State ::= "start" | "left" | "right" | "done"

  configuration <k> $PGM:State </k>

  rule <k> start => left </k> [label(to-left)]
  rule <k> start => right </k> [label(to-right)]
  rule <k> left => done </k> [label(left-done)]
  rule <k> right => done </k> [label(right-done)]
endmodule
