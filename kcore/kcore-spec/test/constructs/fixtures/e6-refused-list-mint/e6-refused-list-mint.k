// The three sort-parametric hooked functions of LIST over MInt{Width} (domains.md), each applied
// once, in a rule of its own labelled with the hook's name, at the instance MInt{64}.
module E6-REFUSED-LIST-MINT
  imports LIST
  imports MINT
  imports INT
  syntax MInt{64}
  syntax KItem ::= go(Int) [symbol(go)]
  rule [list-getMInt]:    <k> go(1) ~> L:List ~> I:MInt{64} => L [ I ] ... </k>
  rule [list-updateMInt]: <k> go(2) ~> L:List ~> I:MInt{64} ~> V:KItem => L [ I <- V ] ... </k>
  rule [list-sizeMInt]:   <k> go(3) ~> L:List => size(L)::MInt{64} ... </k>
endmodule
