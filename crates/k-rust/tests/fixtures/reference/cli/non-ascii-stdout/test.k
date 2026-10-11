module NON-ASCII-STDOUT-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Pgm ::= "print" "(" String ")"
endmodule

module NON-ASCII-STDOUT
  imports NON-ASCII-STDOUT-SYNTAX
  imports DOMAINS

  configuration <k> $PGM:Pgm </k>
                <out stream="stdout"> .List </out>

  rule <k> print(S) => .K </k> <out>... .List => ListItem(S) </out>
endmodule
