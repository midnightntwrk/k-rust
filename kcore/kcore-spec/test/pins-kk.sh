#!/usr/bin/env bash
# The pin of C10's statements (test/PinsKk.lean): kore.k's text as kompile wrote it
# (examples/ref-kk/RefKk/definition.kore) generated with `kcore gen --core` under the namespace
# RefKk into .lake/pins/kk (ignored), built (gen/build.sh: one module a process, one thread,
# 12 GiB memory scope) with the User modules of examples/ref-kk that User.KkThree imports, copied
# in and built in the order of their imports; then the pin file checked against it: the three
# statements and `kk_step` by their types, `sig` and its fields by `rfl`, `succs_name`, and the
# facts the statements rest on (enc_injective, emb_injective, embSt_injective, emb_sorted,
# embD_sorted, encDef_isSome) by their types, with their axioms.
#
# Exit 1 when the package or a User module does not build, or the pin file does not check.
# Usage: test/pins-kk.sh   (from anywhere; the library and `kcore` built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
P=.lake/pins/kk
U=examples/ref-kk/User
rm -rf "$P"; mkdir -p .lake/pins

gen/gen.sh examples/ref-kk/RefKk/definition.kore "$P" RefKk --core > .lake/pins/kk-gen.log 2>&1 \
  || { cat .lake/pins/kk-gen.log; exit 1; }
# the User modules User.KkThree imports, each after the User modules it imports
mods=$(python3 -I - "$U" User.KkThree <<'PY'
import os, re, sys
u, root = sys.argv[1], sys.argv[2]
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    f = os.path.join(u, m.split('.', 1)[1].replace('.', '/') + '.lean')
    if not os.path.exists(f): sys.exit(f'pins-kk: no {f}')
    for line in open(f, encoding='utf-8'):
        r = re.match(r'import\s+(User\.\S+)', line)
        if r: visit(r.group(1))
    order.append(m)
visit(root)
print(' '.join(order))
PY
) || exit 1
mkdir -p "$P/User"
for m in $mods; do f=${m#User.}; f=${f//.//}.lean; mkdir -p "$P/User/$(dirname "$f")"; cp "$U/$f" "$P/User/$f" || exit 1; done
gen/build.sh "$P" $mods || exit 1
LEAN_PATH=$P/.lake/build/lib/lean:$(lake env printenv LEAN_PATH) LEAN_NUM_THREADS=1 \
  systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 1200 \
  "$TC/bin/lean" -j1 test/PinsKk.lean || exit 1
echo "pins on kk: ok ($(echo $mods | wc -w) User modules)"
