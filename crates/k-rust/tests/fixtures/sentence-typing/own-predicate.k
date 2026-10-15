module OWN-PREDICATE
  imports INT
  syntax Foo ::= foo()
  syntax Int ::= isFoo(Int) [function, total, symbol(isFoo)]
  syntax KItem ::= h(Int) | g(Int)
  rule [own]: isFoo(X) => X +Int 1
  rule [use]: h(X) => g(isFoo(X))
endmodule
