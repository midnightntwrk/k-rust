// Two sorts of the text named as a cell and its cell set, the first a subsort of the second.
module RDR-CELLCOLL-OWN
  imports INT
  syntax FooCell ::= foo(Int) [symbol(foo)]
  syntax FooCellSet ::= FooCell | ".FooCellSet" [symbol(dotFoo)]
endmodule
