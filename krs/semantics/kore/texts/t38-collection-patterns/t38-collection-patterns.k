module T38-COLLECTION-PATTERNS
  imports INT
  imports MAP
  imports LIST
  syntax Exp ::= a(Map) | b(List) | k(KItem) | v(KItem)
  rule <k> a((K |-> _) _:Map) => k(K) ... </k>
  rule <k> b(ListItem(X) _:List) => v(X) ... </k>
endmodule
