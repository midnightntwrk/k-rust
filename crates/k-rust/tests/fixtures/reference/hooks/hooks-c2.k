module HOOKS-C2-SYNTAX
  imports DOMAINS-SYNTAX
  imports BYTES-SYNTAX
  syntax Pgm ::= "pc" | "y14" | "y16" | "edges"
endmodule

module HOOKS-C2
  imports DOMAINS
  imports BYTES
  imports HOOKS-C2-SYNTAX
  configuration <k> $PGM:Pgm </k>
  syntax Int ::= i(Int) [function, total]
  rule i(X) => X
  syntax String ::= s(String) [function, total]
  rule s(X) => X
  rule <k> pc => ListItem(substrString(s("hello"), i(-2), i(3))) ListItem(substrString(s("hello"), i(1), i(10))) ListItem(substrString(s("hello"), i(3), i(1))) ListItem(findString(s("hello"), s("l"), i(1))) ListItem(findString(s("hello"), s("l"), i(3))) ListItem(findString(s("hello"), s(""), i(5))) ListItem(findString(s("hello"), s(""), i(6))) ListItem(findString(s("hello"), s("h"), i(-1))) ... </k>
  rule <k> y14 => ListItem(replaceAtBytes(b"abc", i(2), b"xyz")) ... </k>
  rule <k> y16 => ListItem(memsetBytes(b"abc", i(0), i(2), i(65))) ... </k>
  rule <k> edges => ListItem((i(1) |-> 2) <=Map (i(1) |-> 3))
                    ListItem((i(1) |-> 2) <=Map (i(1) |-> 3 i(2) |-> 4))
                    ListItem((i(1) |-> 2 i(5) |-> 6) <=Map (i(1) |-> 2))
                    ListItem(i(1) ^Int i(4294967296))
                    ListItem(lengthString(chrChar(i(55296))))
                    ListItem(ordChar(chrChar(i(55296))))
                    ListItem(lengthString(substrString(s("hello"), i(3), i(1))))
                    ListItem(substrString(s("hello"), i(-3), i(-1))) ... </k>
endmodule
