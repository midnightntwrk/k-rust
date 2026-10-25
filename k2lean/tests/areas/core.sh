# shellcheck shell=bash
# The core area: kimp (goldens and step traces), KRS IMP, determinism along the rule index
# (kimp-d2, ovl), the fixture freekey, SIMPLE and its acceptance against krust, and the libraries
# in the arity-indexed term universe (kimp-ar, simple-ar, kterm-ar).

kore_core() {
  case $1 in
    kimp) f=$KIMP/imp.k m=IMP s=IMP-SYNTAX inc=$KIMP ;;
    kimp-verif) f=$KIMP/imp-verification.k m=IMP-VERIFICATION s=IMP-VERIFICATION-SYNTAX inc=$KIMP ;;
    ovl) f=$DEMOS/k/overlap.k m=OVERLAP s=OVERLAP-SYNTAX inc=$DEMOS/k ;;
    simple) f=$SD/simple-untyped.md m=SIMPLE-UNTYPED s=SIMPLE-UNTYPED-SYNTAX inc=$SD ;;
    kterm) f=$DEMOS/k/term/term.k m=TERM s=TERM-SYNTAX inc=$DEMOS/k/term ;;
    *) return 1 ;;
  esac
}

name_core() {
  case $1 in
    kimp|kimp-d2|kimp-ar) echo KImp ;; krsimp) echo KrsImp ;; ovl) echo KOvl ;;
    simple|simple-ar) echo KSimple ;; freekey) echo FreeKey ;; kterm-ar) echo KTerm ;;
    *) return 1 ;;
  esac
}

# kimp-ar and simple-ar are kimp and SIMPLE in the arity-indexed term universe (`--arity-terms`)
gen_core() {
  case $1 in
    kimp|kimp-ar) GEN_ARGS=(--kore "$(kore_dir kimp)/definition.kore" --runtime "$(kore_dir kimp)/runtime.json"
            --out "$o" --name KImp --prelude ../../lean/prelude
            --lemmas-kore "$(kore_dir kimp-verif)/definition.kore" --open-obligations "$o/open-obligations.txt")
      [ "$1" = kimp-ar ] && GEN_ARGS+=(--arity-terms) ;;
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
    # a definition with one genuine overlap (witnessed), one joinable pair and exclusive pairs
    # (demos/k/overlap.k): `Step.deterministic_of` with `overlaps_witnessed`
    ovl) GEN_ARGS=(--kore "$(kore_dir ovl)/definition.kore" --runtime "$(kore_dir ovl)/runtime.json"
            --out "$o" --name KOvl --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt") ;;
    simple) GEN_ARGS=(--kore "$(kore_dir simple)/definition.kore" --runtime "$(kore_dir simple)/runtime.json"
            --out "$o" --name KSimple --prelude ../../lean/prelude --linear-terms
            --open-obligations "$o/open-obligations.txt") ;;
    simple-ar) GEN_ARGS=(--kore "$(kore_dir simple)/definition.kore" --runtime "$(kore_dir simple)/runtime.json"
            --out "$o" --name KSimple --prelude ../../lean/prelude --arity-terms
            --open-obligations "$o/open-obligations.txt") ;;
    # the generator's fixture whose functions walk maps by free-key patterns (tests/fixtures/freekey)
    freekey) libs_fixture_args "$1" ;;
    # recursive functions whose termination measures the generator synthesizes (demos/k/term)
    kterm-ar) GEN_ARGS=(--kore "$(kore_dir kterm)/definition.kore" --runtime "$(kore_dir kterm)/runtime.json"
            --out "$o" --name KTerm --prelude ../../lean/prelude --arity-terms
            --open-obligations "$o/open-obligations.txt") ;;
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
