requires "static-adjunct.k"

module KRS-M3D-INDUCED-SOURCE-ERROR
  imports KRS-M3D-STATIC
  rule # m3dTotal ( I:Int ) => I requires I
endmodule
