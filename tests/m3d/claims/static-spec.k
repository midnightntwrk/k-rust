// Functional reconstruction of the five independent M3D adjunct claims.
requires "../fixtures/static-adjunct.k"

module KRS-M3D-STATIC-SPEC
  imports KRS-M3D-STATIC

  claim [total-equation]:
    <k> # addOne ( 4 ) => 5 ... </k>

  claim [partial-equation]:
    <k> # nonnegativeIdentity ( 7 ) => 7 ... </k>

  claim [explicit-priority]:
    <k> # priorityChoice ( 0 ) => 111 ... </k>

  claim [static-alias]:
    <k> zeroAlias => 0 ... </k>

  claim [context-alias]:
    <k> double ( 1 + 2 ) => 6 ... </k>
endmodule
