requires "imp.k"

// Two kind 1 invariants of kimp (k2lean/docs/invariants.md): every value the store <env> binds
// is a Value (`envOk`), and none is an Id (`storeNoIds`: on a value that is not an Id, `isId` is
// `false` by its `owise` equation). `k2lean gen --invariant envOk@env --invariant storeNoIds@env`
// states and proves that every rule keeps both.
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
endmodule
