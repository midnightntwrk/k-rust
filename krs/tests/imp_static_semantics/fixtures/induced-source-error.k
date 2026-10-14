requires "static-adjunct.k"

module KRS-IMP-STATIC-INDUCED-SOURCE-ERROR
  imports KRS-IMP-STATIC
  rule # addOne ( I:Int ) => I requires I
endmodule
