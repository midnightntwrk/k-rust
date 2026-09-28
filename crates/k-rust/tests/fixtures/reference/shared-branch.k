module SHARED-BRANCH
  imports DOMAINS

  syntax State ::= "dup" "(" Int ")" | "capture" "(" Int ")" | "a" | "b" | "c" | "end"
  syntax Tree ::= "leaf" | "pair" "(" Tree "," Tree ")"

  configuration <k> $PGM:State </k>
                <s> leaf </s>
                <output stream="stdout"> .List </output>

  rule <k> dup(N) => dup(N -Int 1) </k>
       <s> T:Tree => pair(T, T) </s>
       requires N >Int 0
  rule <k> capture(N) => capture(N -Int 1) </k>
       <s> T:Tree => pair(T, T) </s>
       requires N >Int 0
  rule <k> dup(0) => a </k>
  rule <k> capture(0) => end </k>
       <output>... .List => ListItem("done") </output>
  rule <k> a => b </k>
  rule <k> a => c </k>
endmodule
