#!/usr/bin/env bash
# The pin of row imp's statements (test/PinsKimp.lean): kimp's text as kompile wrote it
# (examples/ref-kimp/RefKimp/definition.kore) generated with `kcore gen --wf` under the namespace
# RefKimp into .lake/pins/kimp (ignored), built (gen/build.sh: one module a process, one thread,
# 12 GiB memory scope) with the consumer's statement (examples/ref-kimp/User/SumSpecStmt.lean, copied
# in as the module User.SumSpecStmt) and the generated one (examples/ref-kimp/User/SumSpecGen.lean,
# as User.SumSpecGen), then the pin file checked against it: `consistent`, `sound_at`,
# `complete_at` and `run_exact` by their types, the consumer's statements by their bodies, and
# `Generated.«sum-spec» = ExpectedKore.«sum-spec»` by `rfl`, `Expected.«sum-spec» →
# ExpectedKore.«sum-spec»` by `AllPath.mono`; the proof of `Expected.«sum-spec»` and its
# matching-logic corollaries (User.SumSpec, User.SumSpecHolds, User.SumSpecML, copied in) by their types.
#
# Before the package is generated, the generated statement is checked as text:
#   regenerated  `k2lean kcore-claims` run with the command of SumSpecGen.lean's header, in a scratch
#                directory (.lake/pins/kimp-claims) holding its inputs (the fixture's spec.kore and
#                the committed examples/ref-kimp/RefKimp/Syntax.lean) at the paths the header names,
#                so that the header is reproduced too; the output must equal the committed
#                SumSpecGen.lean byte for byte
#   text         the body of `Generated.«sum-spec»` (after `: Prop :=` up to the next blank line or
#                `end`) and that of `ExpectedKore.«sum-spec»` in SumSpecStmt.lean, every run of white
#                space made one space and trimmed, are equal strings; nothing else is normalised
# The emitter: $K2LEAN_BIN when set, otherwise built here (`cargo build --locked -p k2lean`) in the
# nearest directory above kcore-spec holding k2lean/crates/k2lean/Cargo.toml (the k-rust checkout,
# which needs its Cargo workspace: Cargo.toml, Cargo.lock, .cargo/, crates/, krs/crates/,
# kink/crates/, k2lean/).
#
# Exit 1 when the regenerated file or the text differs, or the generated package states another text
# for one of the pinned statements, or does not build.
# Usage: test/pins-kimp.sh   (from anywhere; the library and `kcore` built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
P=.lake/pins/kimp
G=.lake/pins/kimp-claims
GEN=examples/ref-kimp/User/SumSpecGen.lean
SPEC=examples/ref-kimp/claims/imp-sum-spec/spec.kore
SYN=examples/ref-kimp/RefKimp/Syntax.lean
rm -rf "$P" "$G"; mkdir -p .lake/pins

if [ -n "${K2LEAN_BIN:-}" ]; then E=$K2LEAN_BIN
else
  R=; d=$K; while [ "$d" != / ]; do d=$(dirname "$d")
    [ -f "$d/k2lean/crates/k2lean/Cargo.toml" ] && { R=$d; break; }; done
  [ -n "$R" ] || { echo "pins-kimp: no k2lean/crates/k2lean above $K: set K2LEAN_BIN, or widen the sparse" \
    "checkout (git sparse-checkout add /Cargo.toml /Cargo.lock /.cargo/ /crates/ /krs/crates/ /kink/crates/ /k2lean/)"; exit 1; }
  (cd "$R" && cargo build -q --locked -p k2lean --bin k2lean) > .lake/pins/k2lean-build.log 2>&1 \
    || { tail -20 .lake/pins/k2lean-build.log; exit 1; }
  E=${CARGO_TARGET_DIR:-$R/target}/debug/k2lean
fi
[ -x "$E" ] || { echo "pins-kimp: no k2lean executable at $E"; exit 1; }
mkdir -p "$G/$(dirname "$SPEC")" "$G/$(dirname "$SYN")" "$G/$(dirname "$GEN")"
cp "$SPEC" "$G/$SPEC" && cp "$SYN" "$G/$SYN" || exit 1
(cd "$G" && "$E" kcore-claims --spec "$SPEC" --syntax "$SYN" --claim IMP-SUM-SPEC.sum-spec --out "$GEN") \
  > .lake/pins/kimp-claims.log 2>&1 || { cat .lake/pins/kimp-claims.log; exit 1; }
cmp -s "$G/$GEN" "$GEN" \
  || { echo "pins-kimp: k2lean kcore-claims writes another $GEN:"; diff "$G/$GEN" "$GEN" | head -30; exit 1; }
python3 -I - "$GEN" 'Generated.«sum-spec»' examples/ref-kimp/User/SumSpecStmt.lean 'ExpectedKore.«sum-spec»' <<'PY' || exit 1
import sys
def body(path, name):
    lines = open(path, encoding='utf-8').read().split('\n')
    head = f'def {name} : Prop :='
    starts = [i for i, l in enumerate(lines) if l.startswith(head)]
    if len(starts) != 1:
        sys.exit(f'pins-kimp: {path}: {len(starts)} lines begin with {head!r}')
    i = starts[0]
    out = [lines[i][len(head):]]
    for l in lines[i + 1:]:
        if l.strip() == '' or l.startswith('end'):
            break
        out.append(l)
    b = ' '.join(' '.join(out).split())
    if not b:
        sys.exit(f'pins-kimp: {path}: {name} has an empty body')
    return b
g, e = body(sys.argv[1], sys.argv[2]), body(sys.argv[3], sys.argv[4])
if g != e:
    k = next((j for j in range(min(len(g), len(e))) if g[j] != e[j]), min(len(g), len(e)))
    sys.exit(f'pins-kimp: {sys.argv[2]} and {sys.argv[4]} differ as text at character {k}:\n'
             f'  generated: ...{g[max(0, k - 40):k + 40]}\n  expected:  ...{e[max(0, k - 40):k + 40]}')
print(f'pins-kimp: {sys.argv[2]} is {sys.argv[4]} as text ({len(g)} characters)')
PY

gen/gen.sh examples/ref-kimp/RefKimp/definition.kore "$P" RefKimp --wf > .lake/pins/kimp-gen.log 2>&1 \
  || { cat .lake/pins/kimp-gen.log; exit 1; }
mkdir -p "$P/User" && cp examples/ref-kimp/User/SumSpecStmt.lean "$GEN" examples/ref-kimp/User/SumSpec.lean \
  examples/ref-kimp/User/SumSpecHolds.lean examples/ref-kimp/User/SumSpecML.lean "$P/User/" || exit 1
gen/build.sh "$P" User.SumSpecStmt User.SumSpecGen User.SumSpec User.SumSpecHolds User.SumSpecML || exit 1
LEAN_PATH=$P/.lake/build/lib/lean:$(lake env printenv LEAN_PATH) LEAN_NUM_THREADS=1 \
  systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 1200 \
  "$TC/bin/lean" -j1 test/PinsKimp.lean || exit 1
echo "pins on kimp: ok"
