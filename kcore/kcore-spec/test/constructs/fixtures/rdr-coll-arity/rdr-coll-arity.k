// A set sort of the text whose element symbol takes two arguments.
module RDR-COLL-ARITY
  imports INT
  syntax MySet [hook(SET.Set)]
  syntax MySet ::= MySet MySet [left, function, hook(SET.concat), symbol(_MySet_), assoc, comm, unit(.MySet), element(MyItem)]
  syntax MySet ::= ".MySet" [function, total, hook(SET.unit), symbol(.MySet)]
  syntax MySet ::= MyItem(Int, Int) [function, total, hook(SET.element), symbol(MyItem)]
endmodule
