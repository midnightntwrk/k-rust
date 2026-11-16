module E3-KAST
  imports INT
  imports ID
  syntax Exp ::= foo(Int, Int) [symbol(foo)] | bar() [symbol(bar)] | baz(Id) [symbol(baz)] | "hashed" [symbol(#hashed)] | "qq" [symbol(qux)]
  syntax KItem ::= h(K) [symbol(h)]
  rule <k> bar() => `foo`(#token("1", "Int"), 2) ... </k>
  rule <k> baz(#token("x", "Id")) => h(bar()) ... </k>
  rule <k> h(_) => `bar`(.KList) ... </k>
  rule <k> foo(_, _) => foo(1 , 2) ... </k>
  rule <k> foo(3, _) => qux(.KList) ... </k>
  rule <k> foo(4, _) => #hashed(.KList) ... </k>
endmodule
