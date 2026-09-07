module HOOKS-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Pgm ::= "pc"
endmodule
module HOOKS
  imports DOMAINS
  imports HOOKS-SYNTAX
  configuration <k> $PGM:Pgm </k>
  syntax Int ::= i(Int) [function, total]
  rule i(X) => X
  syntax String ::= s(String) [function, total]
  rule s(X) => X
  syntax Bytes ::= by(Bytes) [function, total]
  rule by(X) => X
  rule <k> pc => ListItem(substrString(s("hello"), i(-2), i(3))) ListItem(substrString(s("hello"), i(1), i(10))) ListItem(substrString(s("hello"), i(3), i(1))) ListItem(findString(s("hello"), s("l"), i(1))) ListItem(findString(s("hello"), s("l"), i(3))) ListItem(findString(s("hello"), s(""), i(5))) ListItem(findString(s("hello"), s(""), i(6))) ListItem(findString(s("hello"), s("h"), i(-1))) ... </k>
endmodule
