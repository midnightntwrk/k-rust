# shellcheck shell=bash
# The soundness area: `soundness` (ImpTypes: kimp against the type checker demos/k/imp-typing.k,
# library imptypes; ExprTypes: kimp's expression language EXPR against demos/k/expr-typing.k,
# libraries kexpr and exprtypes; ImpPlusTypes: IMP++ of K's tutorial, whose threads are a cell map,
# against demos/k/impplus-typing.k, libraries impplus and impplustypes). Registry: soundness.py.

# IMP++ (K's tutorial, beside SIMPLE's sources)
IMPPP=${IMPPP:-$SD/../../../1_k/4_imp++/lesson_7}

kore_soundness() {
  case $1 in
    imp-typing) f=$DEMOS/k/imp-typing.k m=IMP-TYPING s=IMP-TYPING-SYNTAX inc=$KIMP ;;
    # kimp's expression language (expr.k, whose programs end with a value) and its checker
    expr) f=$KIMP/expr.k m=EXPR s=EXPR-SYNTAX inc=$KIMP ;;
    expr-typing) f=$DEMOS/k/expr-typing.k m=EXPR-TYPING s=EXPR-TYPING-SYNTAX inc=$KIMP ;;
    impplus) f=$IMPPP/imp.k m=IMP s=IMP-SYNTAX inc=$IMPPP ;;
    impplus-typing) f=$DEMOS/k/impplus-typing.k m=IMPPLUS-TYPING s=IMPPLUS-TYPING-SYNTAX inc=$IMPPP ;;
    *) return 1 ;;
  esac
}

name_soundness() {
  case $1 in
    imptypes) echo KImpTypes ;;
    kexpr) echo KExpr ;;
    exprtypes) echo KExprTypes ;;
    impplus) echo KImpPlus ;;
    impplustypes) echo KImpPlusTypes ;;
    *) return 1 ;;
  esac
}

gen_soundness() {
  case $1 in
    imptypes) GEN_ARGS=(--kore "$(kore_dir imp-typing)/definition.kore" --runtime "$(kore_dir imp-typing)/runtime.json"
            --out "$o" --name KImpTypes --prelude ../../lean
            --open-obligations "$o/open-obligations.txt" --extra-fns "typeOf,wt") ;;
    # EXPR and its checker, for ExprTypes
    kexpr) GEN_ARGS=(--kore "$(kore_dir expr)/definition.kore" --runtime "$(kore_dir expr)/runtime.json"
            --out "$o" --name KExpr --prelude ../../lean
            --open-obligations "$o/open-obligations.txt") ;;
    exprtypes) GEN_ARGS=(--kore "$(kore_dir expr-typing)/definition.kore" --runtime "$(kore_dir expr-typing)/runtime.json"
            --out "$o" --name KExprTypes --prelude ../../lean
            --open-obligations "$o/open-obligations.txt" --extra-fns "typeOf") ;;
    # IMP++ and its checker, for ImpPlusTypes
    impplus) GEN_ARGS=(--kore "$(kore_dir impplus)/definition.kore" --runtime "$(kore_dir impplus)/runtime.json"
            --out "$o" --name KImpPlus --prelude ../../lean
            --open-obligations "$o/open-obligations.txt") ;;
    impplustypes) GEN_ARGS=(--kore "$(kore_dir impplus-typing)/definition.kore" --runtime "$(kore_dir impplus-typing)/runtime.json"
            --out "$o" --name KImpPlusTypes --prelude ../../lean
            --open-obligations "$o/open-obligations.txt" --extra-fns "typeOf,typeOfB,wt,wts,printable") ;;
    *) return 1 ;;
  esac
  return 0
}

# ImpTypes: `Tr.lean`, kimp to the type checker, translating programs (`--roots`)
relate_soundness() {
  case $1 in
    ImpTypes) nb=KImpTypes kd=$(kore_dir imp-typing) extra=(--roots "SortStmt,SortExpr") ;;
    ExprTypes) na=KExpr ka=$(kore_dir expr) nb=KExprTypes kd=$(kore_dir expr-typing)
               extra=(--roots "SortExpr") ;;
    ImpPlusTypes) na=KImpPlus ka=$(kore_dir impplus) nb=KImpPlusTypes kd=$(kore_dir impplus-typing)
               extra=(--roots "SortStmts,SortStmt,SortAExp,SortBExp") ;;
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
    # programs end with a value and no cell is typed by hand: `typeOf` accepts them (design.md, §3.3)
    ExprTypes) "$G" soundness --kore-a "$(kore_dir expr)/definition.kore" --name-a KExpr \
        --kore-b "$(kore_dir expr-typing)/definition.kore" --name-b KExprTypes --ns ExprTypes \
        --typing typeOf \
        --out-typing "$DEMOS/ExprTypes/ExprTypes/Typing.lean" --out-soundness "$DEMOS/ExprTypes/ExprTypes/Soundness.lean" ;;
    # threads in a cell map, holes of two sorts, rules of three ranks (K's I/O streams); the
    # checker types statements without variables (`wt`, `wts`, accepting programs) and calls
    # `printable` on `print`'s arguments; a block's saved environment is an item of `<k>`
    ImpPlusTypes) "$G" soundness --kore-a "$(kore_dir impplus)/definition.kore" --name-a KImpPlus \
        --kore-b "$(kore_dir impplus-typing)/definition.kore" --name-b KImpPlusTypes --ns ImpPlusTypes \
        --typing typeOf,typeOfB,wt,wts --aux printable --program wts --env-item Map \
        --out-typing "$DEMOS/ImpPlusTypes/ImpPlusTypes/Typing.lean" --out-soundness "$DEMOS/ImpPlusTypes/ImpPlusTypes/Soundness.lean" ;;
    *) echo "libs_soundness: unknown demo $1" >&2; return 2 ;;
  esac
}

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

gate_soundness() {
  kc kimp
  runs lib imptypes && kc imp-typing && lib imptypes KImpTypes
  if runs demo ImpTypes; then
    phase "demo ImpTypes"
    kc imp-typing && rel ImpTypes
    scaffold soundness-ImpTypes libs_soundness ImpTypes
    dbuild ImpTypes
  fi
  runs lib kexpr && kc expr && lib kexpr KExpr
  runs lib exprtypes && kc expr-typing && lib exprtypes KExprTypes
  if runs demo ExprTypes; then
    phase "demo ExprTypes"
    kc expr && kc expr-typing && rel ExprTypes
    scaffold soundness-ExprTypes libs_soundness ExprTypes
    dbuild ExprTypes
  fi
  runs lib impplus && kc impplus && lib impplus KImpPlus
  # IMP++'s fresh values, a kind 2 invariant over impplus (demos/ImpPlusFresh): what progress at
  # `int` and `spawn` needs, that the next location and thread id are not keys yet
  if runs demo ImpPlusFresh; then
    phase "demo ImpPlusFresh"
    dbuild ImpPlusFresh
  fi
  runs lib impplustypes && kc impplus-typing && lib impplustypes KImpPlusTypes
  if runs demo ImpPlusTypes; then
    phase "demo ImpPlusTypes"
    kc impplus && kc impplus-typing && rel ImpPlusTypes
    scaffold soundness-ImpPlusTypes libs_soundness ImpPlusTypes
    dbuild ImpPlusTypes
  fi
  phase "diff soundness"
  diffs imptypes kexpr exprtypes impplus impplustypes
}
