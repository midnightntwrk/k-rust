# shellcheck shell=bash
# The invariants area: kind 1 invariant libraries (kimpinv, kimpkeys, kimpkeys-hand, kimpfold,
# kimptop, nested, and SIMPLE's simpleinv, simplestore, simplet), KRS IMP's sidecar invariant, the
# negative check, the kind 2 demos (ImpWrites, KrsImpTyping, SimpleEnv) and template.

kore_invariants() {
  case $1 in
    kimp-inv) f=$DEMOS/k/kimp-inv/imp-inv.k m=IMP-INV s=IMP-SYNTAX inc=$KIMP ;;
    kimp-keys) f=$DEMOS/k/kimp-keys/imp-keys.k m=IMP-KEYS s=IMP-SYNTAX inc=$KIMP ;;
    simple-inv) f=$DEMOS/k/simple-inv/simple-inv.k m=SIMPLE-INV s=SIMPLE-UNTYPED-SYNTAX inc=$SD ;;
    *) return 1 ;;
  esac
}

name_invariants() {
  case $1 in
    kimpinv|kimpfold|kimptop) echo KImpInv ;; kimpkeys|kimpkeys-hand) echo KImpKeys ;; nested) echo KNested ;;
    simpleinv|simplestore|simplet) echo KSimpleInv ;;
    *) return 1 ;;
  esac
}

gen_invariants() {
  case $1 in
    kimpinv) GEN_ARGS=(--kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json"
            --out "$o" --name KImpInv --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
            --invariant envOk@env --invariant storeNoIds@env) ;;
    # kimp with the K function `envKeysOk` (demos/k/kimp-keys, the walkthrough of
    # docs/invariants.md, §3); kimpkeys-hand is the same library with one case listed in its
    # open-invariant-cases.txt, so that the case is taken from its hand module
    kimpkeys|kimpkeys-hand) GEN_ARGS=(--kore "$(kore_dir kimp-keys)/definition.kore" --runtime "$(kore_dir kimp-keys)/runtime.json"
            --out "$o" --name KImpKeys --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
            --invariant envKeysOk@env) ;;
    # the same definition with the invariant as a fold with a parameter (`allIs(L, B)`), and as a
    # function of the whole configuration (the top-cell form, `topEnvOk`)
    kimpfold) GEN_ARGS=(--kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json"
            --out "$o" --name KImpInv --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
            --invariant envAll@env) ;;
    kimptop) GEN_ARGS=(--kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json"
            --out "$o" --name KImpInv --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
            --invariant topEnvOk) ;;
    # a cell inside two nested cell maps (tests/fixtures/nested, whose compiled KORE is committed)
    nested) GEN_ARGS=(--kore "$FIXTURES/nested/definition.kore" --runtime "$FIXTURES/nested/runtime.json"
            --out "$o" --name KNested --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
            --invariant even@v) ;;
    # SIMPLE with the K function `holdsOk` (demos/k/simple-inv): a cell predicate of `<holds>`, which
    # is inside the `<thread>` cell map, so it is lifted to "every thread"
    simpleinv) GEN_ARGS=(--kore "$(kore_dir simple-inv)/definition.kore" --runtime "$(kore_dir simple-inv)/runtime.json"
            --out "$o" --name KSimpleInv --prelude ../../lean/prelude --linear-terms
            --open-obligations "$o/open-obligations.txt" --invariant holdsOk@holds) ;;
    # the same definition with "every store value is a Val or undefined", as a function of the `<store>` cell's
    # content and as a function of SIMPLE's top cell `<T>`
    simplestore|simplet) GEN_ARGS=(--kore "$(kore_dir simple-inv)/definition.kore" --runtime "$(kore_dir simple-inv)/runtime.json"
            --out "$o" --name KSimpleInv --prelude ../../lean/prelude --linear-terms
            --open-obligations "$o/open-obligations.txt"
            --invariant "$([ "$1" = simplet ] && echo tStoreOk@T || echo storeOk@store)") ;;
    *) return 1 ;;
  esac
  return 0
}

# libs_gen_ill_typed DIR: KRS IMP with an ill-typed `assign` (krs-imp-ill-typed.py beside libs.sh), with
# the sidecar, into DIR (namespace KrsImp, so its Terms.lean equals krsimp's): the generated proof of the
# declared cell type must fail at `KRS-IMP.assign` (the gate's negative check).
libs_gen_ill_typed() {
  python3 -I "$LIBS_DIR/krs-imp-ill-typed.py" "$KRS/definition.kore" "$1/definition.kore" &&
  "$G" gen --kore "$1/definition.kore" --out "$1" --name KrsImp --prelude ../../lean/prelude \
    --open-obligations "$1/open-obligations.txt" --sidecar "$KRS/k2lean-sidecar.json"
}
