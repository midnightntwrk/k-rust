#!/usr/bin/env bash
# The five literals of examples/ref-kk/User/KimpInst.lean, computed from kimp's text
# (examples/ref-kimp/RefKimp/definition.kore) and printed as the `def`s the module holds:
#   E₀  `KK.encDef` of kimp's semantics, as the reader gives it from the text
#   x₀  the configuration `RefKimp.Claims.inst` (User.SumSpecStmt of ref-kimp)
#   y₀  its one successor by the executable step (`CExec.successorsN`), at HookParams.none
#   t₀  `emb (enc x₀)`, and r₀, `embSt (.next [enc y₀])`, with the embeddings of KKNative.lean
# The module's kernel checks tie each one (`encDef_kimp`, `t₀_tie`, `r₀_tie`, `succs_run`), so what
# is printed here is a proposal: a literal that is not the value fails the module's build.
# Needs ref-kimp built with User.SumSpecStmt (gen/build.sh examples/ref-kimp User.SumSpecStmt).
# Usage: gen/kimp-inst-lits.sh > FILE   (from anywhere; the library built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
W=.lake/kimp-inst; mkdir -p "$W"
cat > "$W/Lits.lean" <<'LEAN'
import User.SumSpecStmt
import KcoreSpec.KKNative
import KcoreSpec.DataCmd
set_option maxRecDepth 1000000
open KCore KCore.KK
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let c ← semanticsOfFile "RefKimp/definition.kore"
  let some E := encDef c | throwError "encDef has no value at kimp's text"
  let x := RefKimp.Claims.inst.val
  let [y] := CExec.successorsN (c.withHooks HookParams.none) 100 x
    | throwError "the configuration has not one successor at the fuel 100"
  let lit := fun (n ty : String) (f : Std.Format) => s!"def {n} : {ty} :=\n  {f.pretty 100}\n"
  IO.println ("\n".intercalate [lit "E₀" "D" (repr E), lit "x₀" "GroundTerm" (repr x),
    lit "y₀" "GroundTerm" (repr y), lit "t₀" "GroundTerm" (repr (Native.emb (enc x))),
    lit "r₀" "GroundTerm" (repr (Native.embSt (.next [enc y])))])
LEAN
out=$(cd examples/ref-kimp && LEAN_PATH=$PWD/.lake/build/lib/lean:$(cd "$K" && lake env printenv LEAN_PATH) \
  LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 600 \
  "$TC/bin/lean" -j1 "$K/$W/Lits.lean" 2>&1) || { echo "$out" >&2; exit 1; }
# the constructors by their short names, and the fields of E₀ to the right of its brace
echo "$out" | python3 -I -c '
import re, sys
ind = False
for l in sys.stdin.read().rstrip("\n").split("\n"):
    for a, b in (("KCore.KK.T.", "T."), ("KCore.GroundTerm.", "GroundTerm."), ("KCore.Lit.", "Lit."),
                 ("KCore.KK.Kind.", "Kind.")):
        l = l.replace(a, b)
    if l.startswith("def ") or l.startswith("  { subs"): ind = False
    elif re.match(r"  (fns|rules) := ", l): ind = True; l = "  " + l
    elif ind and l.strip(): l = "  " + l
    print(l)
'
