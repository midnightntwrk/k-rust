module REACHABILITY
  syntax State ::= "a" [symbol(a)]
                 | "b" [symbol(b)]

  configuration <k> $PGM:State </k>

  rule <k> a => b </k>
  claim <k> a => b </k> [one-path, label(reaches-b)]
endmodule
