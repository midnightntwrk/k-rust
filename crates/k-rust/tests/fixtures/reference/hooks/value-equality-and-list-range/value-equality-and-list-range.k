module HOOKS-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Pgm ::= "pg"
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
  rule <k> pg => ListItem(i(3) ==K i(+3)) ListItem(i(3) ==Int i(+3)) ListItem(i(+3)) ListItem((i(1) |-> 2) ==K (i(1) |-> 2)) ListItem(#if i(1) ==Int i(1) #then 1 #else 2 #fi) ListItem(range(ListItem(i(1)) ListItem(i(2)), i(1), i(1))) ... </k>
endmodule
