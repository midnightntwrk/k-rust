// The emitted `KRS-VISIBILITY` definition plus a module that imports it and
// uses the private `helper(..)` in a rule. K's `private` hides the production
// from every importing module, so Java K and k-rust both reject this rule.
requires "definition.k"

module KRS-VISIBILITY-INDUCED
  imports KRS-VISIBILITY

  rule [use-helper]:
    <k> helper ( 1 ) => 2 ... </k>
endmodule
