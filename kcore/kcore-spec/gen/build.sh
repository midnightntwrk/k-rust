#!/usr/bin/env bash
# Build a package `kcore gen` wrote (ARCHITECTURE.md §3.8): its modules in the order of its
# modules.txt, with --tie also those of its tie.txt, then the user's modules given, each in its own
# process, one thread, under a 12 GiB memory scope (no swap). Oleans under PKG/.lake/build/lib/lean;
# per-module wall time and peak RSS in PKG/.lake/build/log/MODULE.log. Stops at the first failure.
# Usage: gen/build.sh [--tie] [--with OTHERPKG]... [--only] PKG [USER-MODULE...]
#   --with: another built package the user's modules import; --only: skip the package's own modules.
set -u
K=$(cd "$(dirname "$0")/.." && pwd)
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
RT=$K/../../../k2lean/tests/rtime.py
tie=0; only=0; extra=""
while [ $# -gt 0 ]; do case $1 in
  --tie) tie=1; shift;; --only) only=1; shift;;
  --with) extra="$extra:$(cd "$2" && pwd)/.lake/build/lib/lean"; shift 2;;
  *) break;; esac; done
PKG=$(cd "$1" && pwd); shift
B=$PKG/.lake/build/lib/lean; L=$PKG/.lake/build/log; mkdir -p "$B" "$L"
LP=$(cd "$K" && lake env printenv LEAN_PATH)
export LEAN_PATH=$B$extra:$LP LEAN_NUM_THREADS=1
cd "$PKG"
mods=""
[ $only = 1 ] || mods=$(cat modules.txt)
if [ $tie = 1 ]; then
  [ -f tie.txt ] || { echo "$PKG: no tie.txt (generate with kcore gen --tie)"; exit 1; }
  mods="$mods $(cat tie.txt)"
fi
for m in $mods "$@"; do
  f=${m//.//}.lean; o=$B/${m//.//}.olean; mkdir -p "$(dirname "$o")"
  systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
    timeout 2400 python3 "$RT" "$TC/bin/lean" -j1 -o "$o" "$f" > "$L/$m.log" 2>&1 < /dev/null
  r=$(grep -o 'wall [0-9.]* s.*exit [0-9-]*' "$L/$m.log" | sed 's/max child //')
  echo "$m: ${r:-killed (no rtime line: the memory scope or the timeout)}"
  case "$r" in *"exit 0") ;; *) grep -v '^rtime' "$L/$m.log" | head -30; exit 1;; esac
done
echo "built"
