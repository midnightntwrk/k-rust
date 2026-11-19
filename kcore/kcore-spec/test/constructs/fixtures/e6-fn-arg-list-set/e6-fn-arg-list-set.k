// List:set (hook LIST.update) in a function equation's argument pattern.
module E6-FN-ARG-LIST-SET
  imports LIST
  imports INT
  syntax List ::= h(List) [function, symbol(h)]
  rule h(L [ 0 <- 1 ]) => L
endmodule
