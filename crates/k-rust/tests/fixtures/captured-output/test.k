module CAPTURED-OUTPUT-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Pgm ::= "literal"
               | "empty"
               | "stdin"
               | "bottom"
               | "residual"
               | "branch"
               | "done" "(" Int ")"
endmodule

module CAPTURED-OUTPUT
  imports CAPTURED-OUTPUT-SYNTAX
  imports DOMAINS

  configuration <k> $PGM:Pgm </k>
                <saved> $STDIN:String </saved>
                <output stream="stdout"> .List </output>

  rule <k> literal => .K </k> <output>... .List => ListItem("literal output") </output>
  rule <k> empty => .K </k>
  rule <k> stdin => .K </k> <saved> S:String </saved>
       <output>... .List => ListItem(S) ListItem("output") </output>
  rule <k> bottom => .K </k> ensures false
  rule <k> residual => done(?N:Int) </k>
       <output>... .List => ListItem("residual") </output>
       ensures ?N >Int 0
  rule <k> branch => .K </k> <output>... .List => ListItem("first") </output>
  rule <k> branch => .K </k> <output>... .List => ListItem("second") </output>
endmodule
