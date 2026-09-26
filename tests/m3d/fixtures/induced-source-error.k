requires "static-adjunct.k"

module KRS-M3D-INDUCED-SOURCE-ERROR
  imports KRS-M3D-STATIC
  rule # addOne ( I:Int ) => I requires I
endmodule
