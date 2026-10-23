requires "imp.k"

// A kind 1 invariant of kimp (k2lean/docs/invariants.md): every value the store <env> binds
// is a Value. `k2lean gen --invariant envOk@env` states and proves that every rule keeps it.
module IMP-INV
  imports IMP
  imports MAP
  imports LIST
  imports BOOL

  syntax Bool ::= envOk(Map) [function, total]
                | allValues(List) [function, total]
  rule envOk(M) => allValues(values(M))
  rule allValues(.List) => true
  rule allValues(ListItem(V) L) => isValue(V) andBool allValues(L)
endmodule
