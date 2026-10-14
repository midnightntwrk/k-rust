// Functional reconstruction of the five independent IMP static semantics adjunct claims.
requires "../fixtures/static-adjunct.k"

module KRS-IMP-STATIC-SPEC
  imports KRS-IMP-STATIC

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
