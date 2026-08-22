module TRANSITIVE-REACHABILITY
  syntax State ::= "a" [symbol(a)]
                 | "b" [symbol(b)]
                 | "c" [symbol(c)]

  configuration <k> $PGM:State </k>

  rule <k> a => b </k>
  rule <k> b => c </k>

  claim <k> a => c </k> [one-path, label(reaches-c)]
endmodule
