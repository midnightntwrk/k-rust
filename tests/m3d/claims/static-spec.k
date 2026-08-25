// Functional reconstruction of the five independent M3D adjunct claims.
requires "../fixtures/static-adjunct.k"

module KRS-M3D-STATIC-SPEC
  imports KRS-M3D-STATIC

  claim [total-equation]:
    <k> # m3dTotal ( 4 ) => 5 ... </k>

  claim [partial-equation]:
    <k> # m3dPositive ( 7 ) => 7 ... </k>

  claim [explicit-priority]:
    <k> # m3dPriority ( 0 ) => 111 ... </k>

  claim [static-alias]:
    <k> m3dZero => 0 ... </k>

  claim [context-alias]:
    <k> m3dTwice ( 1 + 2 ) => 6 ... </k>
endmodule
