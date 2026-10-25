# shellcheck shell=bash
# The soundness area: `soundness` (ImpTypes: kimp against the type checker demos/k/imp-typing.k,
# library imptypes). Registry: soundness.py.

kore_soundness() {
  case $1 in
    imp-typing) f=$DEMOS/k/imp-typing.k m=IMP-TYPING s=IMP-TYPING-SYNTAX inc=$KIMP ;;
    *) return 1 ;;
  esac
}

name_soundness() {
  case $1 in
    imptypes|imptypes-ps) echo KImpTypes ;;
    *) return 1 ;;
  esac
}

gen_soundness() {
  case $1 in
    imptypes) GEN_ARGS=(--kore "$(kore_dir imp-typing)/definition.kore" --runtime "$(kore_dir imp-typing)/runtime.json"
            --out "$o" --name KImpTypes --prelude ../../lean/prelude
            --open-obligations "$o/open-obligations.txt" --extra-fns "typeOf,wt") ;;
    # imptypes in the per-sort encoding, for ImpTypes: `soundness` writes Typing.lean per-sort
    imptypes-ps) GEN_ARGS=(--kore "$(kore_dir imp-typing)/definition.kore" --runtime "$(kore_dir imp-typing)/runtime.json"
            --out "$o" --name KImpTypes --prelude ../../lean/prelude
            --open-obligations "$o/open-obligations.txt" --extra-fns "typeOf,wt" --per-sort-terms) ;;
    *) return 1 ;;
  esac
  return 0
}

# ImpTypes: `Tr.lean`, kimp to the type checker, translating programs (`--roots`)
relate_soundness() {
  case $1 in
    ImpTypes) nb=KImpTypes kd=$(kore_dir imp-typing) extra=(--roots "SortStmt,SortExpr" --per-sort-terms true) ;;
    *) return 1 ;;
  esac
}

# libs_soundness NS: the generated modules of the type-soundness demo NS around its hand module
# `NS/Store.lean` (ImpTypes: `Typing.lean` before it, `Soundness.lean` after it; kimp against the
# type checker demos/k/imp-typing.k, whose store cell <env> the hand module types by `envTy`).
libs_soundness() {
  case $1 in
    ImpTypes) "$G" soundness --kore-a "$(kore_dir kimp)/definition.kore" --name-a KImp \
        --kore-b "$(kore_dir imp-typing)/definition.kore" --name-b KImpTypes --ns ImpTypes \
        --typing typeOf,wt --store-cell env --store-typing envTy \
        --out-typing "$DEMOS/ImpTypes/ImpTypes/Typing.lean" --out-soundness "$DEMOS/ImpTypes/ImpTypes/Soundness.lean" ;;
    *) echo "libs_soundness: unknown demo $1" >&2; return 2 ;;
  esac
}

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

gate_soundness() {
  kc kimp
  runs lib imptypes && kc imp-typing && lib imptypes KImpTypes
  runs lib imptypes-ps && kc imp-typing && lib imptypes-ps KImpTypes
  if runs demo ImpTypes; then
    phase "demo ImpTypes"
    kc imp-typing && rel ImpTypes
    scaffold soundness-ImpTypes libs_soundness ImpTypes
    dbuild ImpTypes
  fi
  phase "diff soundness"
  diffs imptypes
}
