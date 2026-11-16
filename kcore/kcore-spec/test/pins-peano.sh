#!/usr/bin/env bash
# The generated-package pin (test/PinsPeano.lean): peano's text generated with `kcore gen --core`
# under the namespace PinPeano into .lake/pins/peano (ignored), built (gen/build.sh: one module a
# process, one thread, 12 GiB memory scope), then the pin file checked against it.
# Usage: test/pins-peano.sh   (from anywhere; the library and `kcore` built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
P=.lake/pins/peano
rm -rf "$P"; mkdir -p .lake/pins
gen/gen.sh examples/peano/Peano/definition.kore "$P" PinPeano --core > .lake/pins/peano-gen.log 2>&1 \
  || { cat .lake/pins/peano-gen.log; exit 1; }
gen/build.sh "$P" || exit 1
LEAN_PATH=$P/.lake/build/lib/lean:$(lake env printenv LEAN_PATH) LEAN_NUM_THREADS=1 \
  systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 1200 \
  "$TC/bin/lean" -j1 test/PinsPeano.lean || exit 1
echo "pins on peano: ok"
