#!/usr/bin/env bash
# Run certificates whose step is by a rule that shares its sentence's UNIQUE_ID with another rule:
# the two rules `requires A #Or B` is read as (f2-examples/mlreqorsplit, `go(X) => done requires
# X >Int 0 #Or X <Int -5`; f2-examples/mlreqor, `X >=Int 0 #Or 10 /Int X >Int 0`) and the two rules
# of `p(_:Int) #Or q(_:Int) => b()` (f2-examples/mlvalue). The hand-built certificates of test/certs
# (rpcrun.py's JSON) step `go(-6)` and `q(1)` to `done` and `b`, by the second rule of each pair
# (reqor-second, orsplit-second), and `go(5)` to `done` where both rules of mlreqor step
# (reqor-overlap): both are readings of the one sentence the id names, each step is a step of the
# semantics, so the certificate is valid and `kcore gen` takes the first of them. `kcore gen` into
# .lake/cert-shared-uid (ignored) must give each step that rule's number: the rules of the step's
# id are found by the id in the generated package (`kcore rule-ids` on the package's
# definition.kore, the text its `defn` is the parse of), not written here, so the test does not
# depend on the order in which the reader numbers the rules. The certificate module of each package
# is built (its imports first: one module a process, one thread, 12 GiB memory scope), so that the
# kernel checks the run (`checkRun`) and the stuck end (`stuckCheck`). A certificate whose rule id
# is shared and that no rule of it justifies must be refused by `kcore gen` with the step and the
# rules named: reqor-none (go(-6) to itself). Last, the example packages with certificates (peano,
# prio) regenerate identically (test/regen.sh).
# Usage: test/cert-shared-uid.sh   (from anywhere; the library and `kcore` built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
O=.lake/cert-shared-uid; rm -rf "$O"; mkdir -p "$O"
fail=0
# The rule id of the first step of the certificate test/certs/CERT.cert.json.
uidOf() { python3 -I -c 'import json, sys; print(json.load(open(sys.argv[1]))["steps"][0]["uid"])' "test/certs/$1.cert.json"; }
# The numbers of the rules of the package OUT whose id is that of CERT's step, in order.
group() { .lake/build/bin/kcore rule-ids "$1/CertUid/definition.kore" | awk -v u="$(uidOf "$2")" '$2 == u { print $1 }'; }
# name|kore|certificate|which rule of the id's the step is by (1 the first)
ok=("reqor|f2-examples/mlreqorsplit.kompile.kore|reqor-second|2"
    "orsplit|f2-examples/mlvalue.kompile.kore|orsplit-second|2"
    "overlap|f2-examples/mlreqor.kompile.kore|reqor-overlap|1")
for e in "${ok[@]}"; do
  IFS='|' read -r n kore cert which <<< "$e"
  gen/gen.sh "$kore" "$O/$n" CertUid --cert "s=test/certs/$cert.cert.json" > "$O/$n-gen.log" 2>&1 \
    || { echo "cert-shared-uid: $n: gen failed"; tail -3 "$O/$n-gen.log"; fail=1; continue; }
  g=$(group "$O/$n" "$cert" | tr '\n' ' ')
  [ "$(echo $g | wc -w)" = 2 ] || { echo "cert-shared-uid: $n: the step's id is the id of rules [$g], not of two"; fail=1; continue; }
  want=$(echo $g | cut -d' ' -f"$which")
  got=$(grep -A1 '^def s_steps' "$O/$n/CertUid/Certs/s.lean" | tail -1 | sed -n 's/^  (\([0-9]*\), .*/\1/p')
  [ "$got" = "$want" ] || { echo "cert-shared-uid: $n: the step is by rule $got, not $want (rule $which of [$g])"; fail=1; }
done
no=("none|f2-examples/mlreqorsplit.kompile.kore|reqor-none")
for e in "${no[@]}"; do
  IFS='|' read -r n kore cert <<< "$e"
  if gen/gen.sh "$kore" "$O/$n" CertUid --cert "s=test/certs/$cert.cert.json" > "$O/$n-gen.log" 2>&1; then
    echo "cert-shared-uid: $n: gen accepted the certificate"; fail=1
  else
    g=$(group "$O/$n" "$cert" | paste -sd, | sed 's/,/, /g')
    grep -qF "step 1: rule id $(uidOf "$cert") is the id of rules [$g], and none of them" "$O/$n-gen.log" \
      || { echo "cert-shared-uid: $n: not the expected refusal (rules [$g])"; tail -3 "$O/$n-gen.log"; fail=1; }
  fi
done
[ $fail = 0 ] || exit 1
LP=$(lake env printenv LEAN_PATH)
for n in reqor orsplit overlap; do
  P=$K/$O/$n; B=$P/.lake/build/lib/lean; mkdir -p "$B"
  mods=$(sed '/^CertUid\.Certs\.s$/q' "$P/modules.txt")
  for m in $mods; do
    f=${m//.//}.lean; o=$B/${m//.//}.olean; mkdir -p "$(dirname "$o")"
    (cd "$P" && LEAN_PATH=$B:$LP LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G \
      -p MemorySwapMax=0 timeout 2400 "$TC/bin/lean" -j1 -o "$o" "$f") > "$K/$O/$n-$m.log" 2>&1 < /dev/null \
      || { echo "cert-shared-uid: $n: $m does not build"; head -20 "$K/$O/$n-$m.log"; exit 1; }
  done
done
test/regen.sh peano prio || { echo "cert-shared-uid: a package with certificates does not regenerate identically"; exit 1; }
echo "cert-shared-uid: steps by the second rule of a shared id (mlreqorsplit, mlvalue) and by the first of two that both step (mlreqor) resolved by the id and checked by the kernel; none refused; peano, prio regenerate identically: ok"
