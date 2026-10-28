# shellcheck shell=bash
# The core area: kimp (goldens and step traces), KRS IMP, determinism along the rule index
# (kimp-d2, ovl), rules with `ensures` (ens), the fixture freekey, SIMPLE and its acceptance against
# krust, the synthesized termination measures (kterm-ar). Registry: core.py.

kore_core() {
  case $1 in
    kimp) f=$KIMP/imp.k m=IMP s=IMP-SYNTAX inc=$KIMP ;;
    kimp-verif) f=$KIMP/imp-verification.k m=IMP-VERIFICATION s=IMP-VERIFICATION-SYNTAX inc=$KIMP ;;
    ovl) f=$DEMOS/k/overlap.k m=OVERLAP s=OVERLAP-SYNTAX inc=$DEMOS/k ;;
    ens) f=$DEMOS/k/ensures.k m=ENSURES s=ENSURES-SYNTAX inc=$DEMOS/k ;;
    simple) f=$SD/simple-untyped.md m=SIMPLE-UNTYPED s=SIMPLE-UNTYPED-SYNTAX inc=$SD ;;
    kterm) f=$DEMOS/k/term/term.k m=TERM s=TERM-SYNTAX inc=$DEMOS/k/term ;;
    *) return 1 ;;
  esac
}

name_core() {
  case $1 in
    kimp|kimp-d2) echo KImp ;; krsimp) echo KrsImp ;; ovl) echo KOvl ;; ens) echo KEns ;;
    simple) echo KSimple ;; freekey) echo FreeKey ;; symcoll) echo SymColl ;; alias) echo KAlias ;;
    kterm-ar) echo KTerm ;; overload) echo KOverload ;;
    *) return 1 ;;
  esac
}

gen_core() {
  case $1 in
    kimp) GEN_ARGS=(--kore "$(kore_dir kimp)/definition.kore" --runtime "$(kore_dir kimp)/runtime.json"
            --out "$o" --name KImp --prelude ../../lean/prelude
            --lemmas-kore "$(kore_dir kimp-verif)/definition.kore" --open-obligations "$o/open-obligations.txt") ;;
    # kimp with one exclusive pair of rules listed as overlapping (`--det2-overlap`), so that the
    # conditional statements of determinism (`Step.deterministic_of`) are built too;
    # and its Equations in parts of weight at most 30 (kimp's whole is 84), so that the parts, their
    # aggregating module and `open-from-log` over them are built and checked against kimp's counts
    kimp-d2) GEN_ARGS=(--kore "$(kore_dir kimp)/definition.kore" --runtime "$(kore_dir kimp)/runtime.json"
            --out "$o" --name KImp --prelude ../../lean/prelude
            --lemmas-kore "$(kore_dir kimp-verif)/definition.kore" --open-obligations "$o/open-obligations.txt"
            --det2 --det2-overlap "IMP.if-true,IMP.if-false" --equations-part-weight 30) ;;
    krsimp) GEN_ARGS=(--kore "$KRS/definition.kore" --out "$o" --name KrsImp --prelude ../../lean/prelude
            --open-obligations "$o/open-obligations.txt" --sidecar "$KRS/k2lean-sidecar.json") ;;
    # a definition with two genuine overlaps (witnessed; one reads a map cell), one joinable pair
    # and exclusive pairs (demos/k/overlap.k): `Step.deterministic_of` with `overlaps_witnessed`
    ovl) GEN_ARGS=(--kore "$(kore_dir ovl)/definition.kore" --runtime "$(kore_dir ovl)/runtime.json"
            --out "$o" --name KOvl --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt") ;;
    # rules with `ensures` clauses (demos/k/ensures.k): steps only where the ensures holds, apart
    # by their ensures, and an overlap where both hold (witnessed)
    ens) GEN_ARGS=(--kore "$(kore_dir ens)/definition.kore" --runtime "$(kore_dir ens)/runtime.json"
            --out "$o" --name KEns --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt") ;;
    simple) GEN_ARGS=(--kore "$(kore_dir simple)/definition.kore" --runtime "$(kore_dir simple)/runtime.json"
            --out "$o" --name KSimple --prelude ../../lean/prelude
            --open-obligations "$o/open-obligations.txt") ;;
    # the generator's fixture whose functions walk maps by free-key patterns (tests/fixtures/freekey)
    freekey) libs_fixture_args "$1" ;;
    # the fixture whose simplifications are domains.md's over maps and sets (tests/fixtures/symcoll)
    symcoll) libs_fixture_args "$1" ;;
    # the fixture of alias patterns in function equations (tests/fixtures/alias)
    alias) libs_fixture_args "$1" ;;
    # the fixture of function equations over an overloaded list (tests/fixtures/overload)
    overload) libs_fixture_args "$1" ;;
    # recursive functions whose termination measures the generator synthesizes (demos/k/term),
    # and least fixed points where K's rewriting diverges (term-termination.toml)
    kterm-ar) GEN_ARGS=(--kore "$(kore_dir kterm)/definition.kore" --runtime "$(kore_dir kterm)/runtime.json"
            --out "$o" --name KTerm --prelude ../../lean/prelude
            --termination "$DEMOS/k/term/term-termination.toml" --open-obligations "$o/open-obligations.txt") ;;
    *) return 1 ;;
  esac
  return 0
}

# libs_goldens SCRATCH INTERPRETER [DIR]: kimp's golden cases and step traces (KImpTest/Goldens.lean,
# KImpTest/Traces.lean) for library DIR (default kimp); INTERPRETER is K's LLVM interpreter of kimp.
libs_goldens() {
  "$G" goldens --kore "$(kore_dir kimp)/definition.kore" --name KImp --krust "$KRUST" --definition "$(kore_dir kimp)" \
    --goldens "$GOLDENS/krs-reference" --goldens "$GOLDENS/kimp-llvm" \
    --lean-out "$GEN/${3:-kimp}/KImpTest/Goldens.lean" --scratch "$1" --interpreter "$2" \
    --depths krs-block-sequence:30 --depths example-sumto10:404:4 --depths example-gcd-while:163:3
}

# libs_simple_cases: set the array LIBS_SIMPLE_CASES to the `--case` arguments of SIMPLE's tests
# (the modes of K's test Makefile: `--search` tests, `--search --bound 5`).
libs_simple_cases() {
  LIBS_SIMPLE_CASES=()
  local f b spec
  for f in "$SD"/tests/diverse/*.simple "$SD"/tests/exceptions/*.simple "$SD"/tests/threads/*.simple; do
    b=$(basename "$f" .simple); spec="$b=$f"
    [ -f "$f.in" ] && spec="$spec@$f.in"
    case $b in
      exceptions_07|threads_01|threads_02|threads_04|threads_06|threads_09|div-nondet) spec="$spec!search" ;;
      threads_05) spec="$spec!search:5" ;;
    esac
    LIBS_SIMPLE_CASES+=(--case "$spec")
  done
}

# libs_cases OUT: SIMPLE's cases (needs libs_simple_cases first).
libs_cases() {
  "$G" cases --kore "$(kore_dir simple)/definition.kore" --name KSimple --krust "$KRUST" --definition "$(kore_dir simple)" \
    --sort Stmt --lean-out "$1" "${LIBS_SIMPLE_CASES[@]}"
}

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

needs_core() {
  if runs lib simple; then
    [ -d "$SD" ] || need "SIMPLE's sources at $SD (set GATE_K_CHECKOUT)"
  fi
  return 0
}

# K's LLVM interpreter of kimp, a second executor that the step traces compare krust and the Lean
# semantics with; built once per kimp source and cached (LLVM is its directory)
LLVM=''
kimp_llvm() {
  [ -n "$LLVM" ] && return 0
  phase llvm
  local key tmp
  key=$(cd "$KIMP" && find . -type f | sort | xargs sha256sum | sha256sum | cut -c1-12)
  LLVM=$CACHE/kimp-llvm-$key
  # a cache entry is written under a name of this run's own and renamed into place, so a run that
  # shares the cache never reads a partial one; when two runs build it at once, the first rename
  # wins and the other run discards its copy (the interpreter does not depend on its directory's name)
  if [ ! -x "$LLVM/interpreter" ]; then
    [ -e "$LLVM" ] && mv "$LLVM" "$LLVM.partial.$$" && rm -rf "$LLVM.partial.$$"   # left by an older gate
    tmp=$LLVM.tmp.$$
    rm -rf "$tmp"
    if K_OPTS="-Xmx4096m -Xss4m" "$KOMPILE" "$KIMP/imp.k" --backend llvm --main-module IMP --syntax-module IMP-SYNTAX \
         --output-definition "$tmp" --warnings none -I "$KIMP" > "$L/kompile-llvm.log" 2>&1; then
      mv -T "$tmp" "$LLVM" 2> /dev/null || rm -rf "$tmp"
      ok kompile-llvm
    else rm -rf "$tmp"; bad kompile-llvm "$L/kompile-llvm.log"; fi
  fi
}
kimp_goldens() { # DIR: the goldens and traces of kimp's library DIR, after its generation
  kimp_llvm
  if libs_goldens "$W/goldens-tmp" "$LLVM/interpreter" "$1" > "$L/goldens.log" 2>&1; then ok goldens "$L/goldens.log"
  else bad goldens "$L/goldens.log"; fi
}
kimp_tests() { # DIR [SUB]: build and run kimp's test driver of library DIR (goldens and traces), into measured/SUB
  phase "$1 tests"
  local m=$MEAS${2:+/$2}; mkdir -p "$m"
  if lbuild "$GEN/$1" "build-$1-test" kimp-test; then
    "$GEN/$1/.lake/build/bin/kimp-test" --toml "$m/goldens.toml" > "$m/kimp-test.out" 2> "$L/$1-test.err" \
      && ok "$1-test" "$m/kimp-test.out" || bad "$1-test" "$m/kimp-test.out"
  else bad "build $1-test" "$L/build-$1-test.log"; fi
}
lib_simple() { # DIR [SUB]: generate, cases, build, guard, run the cases, acceptance table into measured/SUB
  local d=$1 o=$GEN/$1 m=$MEAS${2:+/$2}; mkdir -p "$m"
  lib_open "$d"
  genlib "$d" || { bad "gen $d" "$L/gen-$d.log"; return 1; }
  # the cases' expected results come from krust runs (about a minute); they are cached under the
  # hash of everything they depend on: the compiled definition, krust, the generator, the tests
  local key; key=$( { sha256sum "$KO/simple/definition.kore" "$KRUST" "$G"; printf '%s\n' "${LIBS_SIMPLE_CASES[@]}";
    cat "$SD"/tests/*/*.simple* 2>/dev/null; } | sha256sum | cut -c1-16)
  local cached=$CACHE/simple-cases-$key.lean
  if [ -f "$cached" ]; then
    cp "$cached" "$o/KSimpleTest/Cases.lean"; echo "cached $cached" > "$L/cases-$d.log"
  else
    libs_cases "$o/KSimpleTest/Cases.lean" > "$L/cases-$d.log" 2>&1 \
      || { bad "cases $d" "$L/cases-$d.log"; return 1; }
    # written under a name of this run's own and renamed into place, as kimp's interpreter
    cp "$o/KSimpleTest/Cases.lean" "$cached.tmp.$$" && mv -f "$cached.tmp.$$" "$cached"
  fi
  eqns "$d" KSimple || return 1
  lbuild "$o" "build-$d" KSimple || { bad "build $d" "$L/build-$d.log"; return 1; }
  ok "build $d" "$L/build-$d.log"
  lbuild "$o" "build-$d-guard" KSimpleTest.Axioms || { bad "guard $d" "$L/build-$d-guard.log"; return 1; }
  ok "guard $d" "$L/build-$d-guard.log"
  # the fuel twins (as `lib` builds them), before any demo imports them
  if [ -f "$o/KSimple/Fuel.lean" ]; then
    lbuild "$o" "build-$d-fuel" KSimple.Fuel || { bad "fuel $d" "$L/build-$d-fuel.log"; return 1; }
    ok "fuel $d" "$L/build-$d-fuel.log"
  fi
  lbuild "$o" "build-$d-test" ksimple-test || { bad "build ksimple-test" "$L/build-$d-test.log"; return 1; }
  "$o/.lake/build/bin/ksimple-test" > "$L/$d-test.out" 2>&1
  python3 -I "$SELF/tests/simple-acceptance.py" "$L/$d-test.out" "$SD/tests" "$KRUST" "$KO/simple" \
    "$m/simple-acceptance.toml" > "$m/simple-acceptance.md" 2> "$L/$d-acceptance.err"
}

gate_core() {
  if runs lib kimp; then
    kc kimp && kc kimp-verif && lib kimp KImp kimp_goldens kimp && kimp_tests kimp
  fi
  # kimp with determinism along the rule index: Terms … Equations are kimp's, so its build starts
  # from kimp's (only Determinism and the guard differ)
  if runs lib kimp-d2; then
    seed_lake kimp-d2 kimp
    kc kimp && kc kimp-verif && lib kimp-d2 KImp
  fi
  runs lib krsimp && lib krsimp KrsImp
  runs lib ovl && kc ovl && lib ovl KOvl
  runs lib ens && kc ens && lib ens KEns
  # the fixture whose function equations match maps by free-key patterns (`MapHook.chooseFirst`)
  runs lib freekey && lib freekey FreeKey
  # the fixture of `MAP-SYMBOLIC`'s and `SET-SYMBOLIC`'s simplifications (the collection laws)
  runs lib symcoll && lib symcoll SymColl
  # the fixture of alias patterns (`P #as X`) in equations and owise competitors
  runs lib alias && lib alias KAlias
  # the fixture of equations over an overloaded list, matched modulo its overload axioms
  runs lib overload && lib overload KOverload
  # recursive functions whose termination measures the generator synthesizes (demos/k/term);
  # its least fixed points diverge, proved in the hand module KTerm/DivergesHand.lean and
  # checked under the axiom guard (KTermTest/Diverges.lean)
  runs lib kterm-ar && kc kterm && lib kterm-ar KTerm
  # the checks of `#k2l_refuted` (a refutation's form, restatements, the parameters' closure, sorry)
  if (cd "$T/lean/prelude" && "$RT" lake env lean "$D/k/refuted/refuted-check.lean") > "$L/refuted-check.log" 2>&1
  then ok "refuted check" "$L/refuted-check.log"; else bad "refuted check" "$L/refuted-check.log"; fi
  # the checks of `#k2l_proves` (a proof's form: the statement named or written out, its closure, axioms)
  if (cd "$T/lean/prelude" && "$RT" lake env lean "$D/k/proves/proves-check.lean") > "$L/proves-check.log" 2>&1
  then ok "proves check" "$L/proves-check.log"; else bad "proves check" "$L/proves-check.log"; fi
  if runs lib simple; then
    phase "lib simple"
    kc simple && libs_simple_cases && lib_simple simple && ok "simple acceptance" "$MEAS/simple-acceptance.md"
  fi
  phase "diff core"
  diffs kimp krsimp simple
}
