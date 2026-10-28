import Lake
open Lake DSL

/-- A user's project (PKG-7): a generated K semantics (`Params`, the generator's `params` fixture),
an external library implementing one of its hooks (`HexLib`), and the user's own statements and
executable, all through Lake. -/
package «Consumer» where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- the k2lean package at the commit the library was generated for, required by the root too: Lake
-- resolves a package by name, the root's requirement first (the gate rewrites this line to a
-- local clone of the tree under test)
require k2lean from git "https://github.com/midnightntwrk/k-rust" @ "COMMIT" / "k2lean/lean"
-- the generated library (`k2lean gen … --out ../params --prelude-git URL@COMMIT`)
require «Params» from "../params"
-- the external library, which knows nothing of k2lean
require «HexLib» from "../HexLib"

@[default_target]
lean_lib Consumer

/-- The generated run driver at the user's implementation of the hooks (`ParamsBench.benchMain`). -/
lean_exe «consumer-run» where
  root := `Consumer.Run
