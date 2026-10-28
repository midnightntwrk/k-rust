import Lake
open Lake DSL

/-- kimp's expression language EXPR is type-sound for the K type checker
`k/expr-typing.k`. -/
package «ExprTypes» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «KExpr» from "../../generated/kexpr"
require «KExprTypes» from "../../generated/exprtypes"

@[default_target]
lean_lib ExprTypes
