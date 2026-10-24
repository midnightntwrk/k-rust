requires "imp.k"

// Kind 1 invariants of kimp (k2lean/docs/invariants.md), K functions that the generator states
// and proves preserved:
// - envOk@env: every value the store <env> binds is a Value (a `values` fold);
// - storeNoIds@env: no value the store binds is an Id (on a value that is not an Id, `isId` is
//   `false` by its `owise` equation); `k2lean gen --invariant envOk@env --invariant
//   storeNoIds@env` states and proves that every rule keeps both;
// - envAll@env: the same as envOk, through a fold with a parameter (`allIs(L, B)`: every
//   element's `isValue` is `B`, here `true`);
// - topEnvOk: the same, as a function of the whole configuration (the top-cell form), whose
//   one equation matches the cells <k> and <env>.
module IMP-INV
  imports IMP
  imports MAP
  imports LIST
  imports BOOL

  syntax Bool ::= envOk(Map) [function, total]
                | allValues(List) [function, total]
                | storeNoIds(Map) [function, total]
                | noIds(List) [function, total]
  rule envOk(M) => allValues(values(M))
  rule allValues(.List) => true
  rule allValues(ListItem(V) L) => isValue(V) andBool allValues(L)
  rule storeNoIds(M) => noIds(values(M))
  rule noIds(.List) => true
  rule noIds(ListItem(X) L) => notBool isId(X) andBool noIds(L)

  syntax Bool ::= envAll(Map) [function, total]
                | allIs(List, Bool) [function, total]
  rule envAll(M) => allIs(values(M), true)
  rule allIs(.List, _) => true
  rule allIs(ListItem(V) L, B) => (isValue(V) ==Bool B) andBool allIs(L, B)

  syntax Bool ::= topEnvOk(GeneratedTopCell) [function, total]
  rule topEnvOk(<generatedTop> <k> _ </k> <env> E </env> _ </generatedTop>) => allValues(values(E))
endmodule
