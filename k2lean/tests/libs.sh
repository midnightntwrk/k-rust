# shellcheck shell=bash
# The generator invocations of every k2lean library, relation and test-data file, in one place.
# Sourced (not run) by k2lean/tests/gate.sh and k2lean/demos/regen.sh, so a flag is changed once
# and every caller (the gate on its copies included) uses it.
#
# The caller sets, before calling a function:
#   G        the k2lean binary
#   GEN      the libraries' output root (a `generated/` directory next to `lean/prelude`: each
#            library requires the prelude as ../../lean/prelude)
#   DEMOS    the demos root (a `demos/` directory): relations write `DEMOS/NS/...`
#   KRS      the directory of the KRS IMP KORE (`demos/k/krs-imp`)
#   FIXTURES the generator's fixtures (`tests/fixtures`): the `nested` library reads its compiled KORE
#   KRUST    krust; BUILTIN, K's builtin include directory
#   KIMP     kimp's K sources (imp-semantics)
#   SD       SIMPLE's K sources (for libs_simple_cases, and the simple and simple-inv compiles)
#   GOLDENS  the golden cases of kimp (k2lean/tests/goldens; only for libs_goldens)
# and defines the function `kore_dir NAME`, which prints the directory of the compiled KORE of
# NAME (kimp, kimp-verif, kimp-inv, kimp-keys, imp-typing, kmut, simple, simple-inv, simple-variant, kterm), so that each caller keeps its own layout.

# libs_kcompile NAME: compile NAME's K definition with krust into `kore_dir NAME`.
libs_kcompile() {
  local out; out=$(kore_dir "$1")
  local f m s inc
  case $1 in
    kimp) f=$KIMP/imp.k m=IMP s=IMP-SYNTAX inc=$KIMP ;;
    kimp-verif) f=$KIMP/imp-verification.k m=IMP-VERIFICATION s=IMP-VERIFICATION-SYNTAX inc=$KIMP ;;
    kimp-inv) f=$DEMOS/k/kimp-inv/imp-inv.k m=IMP-INV s=IMP-SYNTAX inc=$KIMP ;;
    kimp-keys) f=$DEMOS/k/kimp-keys/imp-keys.k m=IMP-KEYS s=IMP-SYNTAX inc=$KIMP ;;
    imp-typing) f=$DEMOS/k/imp-typing.k m=IMP-TYPING s=IMP-TYPING-SYNTAX inc=$KIMP ;;
    kmut) f=$DEMOS/k/kimp-mutant/imp.k m=IMP s=IMP-SYNTAX inc=$DEMOS/k/kimp-mutant ;;
    simple) f=$SD/simple-untyped.md m=SIMPLE-UNTYPED s=SIMPLE-UNTYPED-SYNTAX inc=$SD ;;
    simple-inv) f=$DEMOS/k/simple-inv/simple-inv.k m=SIMPLE-INV s=SIMPLE-UNTYPED-SYNTAX inc=$SD ;;
    # SIMPLE written differently (tests/simple-variant.py: constructors with other symbols, rules
    # in another order), the other side of the relation demos/SimpleRel
    simple-variant) mkdir -p "$out.src" &&
      python3 -I "$(dirname "${BASH_SOURCE[0]}")/simple-variant.py" "$SD/simple-untyped.md" "$out.src/simple-variant.md" || return 1
      f=$out.src/simple-variant.md m=SIMPLE-UNTYPED s=SIMPLE-UNTYPED-SYNTAX inc=$SD ;;
    kterm) f=$DEMOS/k/term/term.k m=TERM s=TERM-SYNTAX inc=$DEMOS/k/term ;;
    *) echo "libs_kcompile: unknown definition $1" >&2; return 2 ;;
  esac
  "$KRUST" kcompile "$f" --main-module "$m" --syntax-module "$s" --output-directory "$out" \
    --builtin-directory "$BUILTIN" -I "$inc"
}

# libs_name DIR: the Lean namespace of library DIR.
libs_name() {
  case $1 in
    kimp|kimp-d2|kimp-ar) echo KImp ;; kimpinv|kimpfold|kimptop) echo KImpInv ;; kimpkeys|kimpkeys-hand) echo KImpKeys ;; krsimp) echo KrsImp ;; kmut) echo KMut ;; imptypes) echo KImpTypes ;;
    simple|simple-ar) echo KSimple ;; simpleinv|simplestore|simplet) echo KSimpleInv ;; nested) echo KNested ;; simplev) echo KSimpleV ;;
    peano) echo Peano ;; peanob) echo PeanoB ;; cellmap) echo CellMap ;; cellmapb) echo CellMapB ;; freekey) echo FreeKey ;; kterm-ar) echo KTerm ;;
    *) echo "libs_name: unknown library $1" >&2; return 2 ;;
  esac
}

# libs_gen DIR: generate library DIR into GEN/DIR, with its open-obligation list. kimp-ar and
# simple-ar are kimp and SIMPLE in the arity-indexed term universe (`--arity-terms`).
libs_gen() {
  local o=$GEN/$1
  case $1 in
    kimp|kimp-ar) "$G" gen --kore "$(kore_dir kimp)/definition.kore" --runtime "$(kore_dir kimp)/runtime.json" \
            --out "$o" --name KImp --prelude ../../lean/prelude \
            --lemmas-kore "$(kore_dir kimp-verif)/definition.kore" --open-obligations "$o/open-obligations.txt" \
            $([ "$1" = kimp-ar ] && echo --arity-terms) ;;
    # kimp with determinism along the rule index (`--det2`), and one exclusive pair of rules listed
    # as overlapping, so that the conditional statements (`Step.deterministic_of`) are built too;
    # and its Equations in parts of weight at most 30 (kimp's whole is 84), so that the parts, their
    # aggregating module and `open-from-log` over them are built and checked against kimp's counts
    kimp-d2) "$G" gen --kore "$(kore_dir kimp)/definition.kore" --runtime "$(kore_dir kimp)/runtime.json" \
            --out "$o" --name KImp --prelude ../../lean/prelude \
            --lemmas-kore "$(kore_dir kimp-verif)/definition.kore" --open-obligations "$o/open-obligations.txt" \
            --det2 --det2-overlap IMP.if-true,IMP.if-false --equations-part-weight 30 ;;
    kimpinv) "$G" gen --kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json" \
            --out "$o" --name KImpInv --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt" \
            --invariant envOk@env --invariant storeNoIds@env ;;
    # kimp with the K function `envKeysOk` (demos/k/kimp-keys, the walkthrough of
    # docs/invariants.md, §3); kimpkeys-hand is the same library with one case listed in its
    # open-invariant-cases.txt, so that the case is taken from its hand module
    kimpkeys|kimpkeys-hand) "$G" gen --kore "$(kore_dir kimp-keys)/definition.kore" --runtime "$(kore_dir kimp-keys)/runtime.json" \
            --out "$o" --name KImpKeys --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt" \
            --invariant envKeysOk@env ;;
    # the same definition with the invariant as a fold with a parameter (`allIs(L, B)`), and as a
    # function of the whole configuration (the top-cell form, `topEnvOk`)
    kimpfold) "$G" gen --kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json" \
            --out "$o" --name KImpInv --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt" \
            --invariant envAll@env ;;
    kimptop) "$G" gen --kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json" \
            --out "$o" --name KImpInv --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt" \
            --invariant topEnvOk ;;
    # a cell inside two nested cell maps (tests/fixtures/nested, whose compiled KORE is committed)
    nested) "$G" gen --kore "$FIXTURES/nested/definition.kore" --runtime "$FIXTURES/nested/runtime.json" \
            --out "$o" --name KNested --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt" \
            --invariant even@v ;;
    krsimp) "$G" gen --kore "$KRS/definition.kore" --out "$o" --name KrsImp --prelude ../../lean/prelude \
            --open-obligations "$o/open-obligations.txt" --sidecar "$KRS/k2lean-sidecar.json" ;;
    kmut) "$G" gen --kore "$(kore_dir kmut)/definition.kore" --runtime "$(kore_dir kmut)/runtime.json" \
            --out "$o" --name KMut --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt" ;;
    imptypes) "$G" gen --kore "$(kore_dir imp-typing)/definition.kore" --runtime "$(kore_dir imp-typing)/runtime.json" \
            --out "$o" --name KImpTypes --prelude ../../lean/prelude \
            --open-obligations "$o/open-obligations.txt" --extra-fns typeOf,wt ;;
    simple) "$G" gen --kore "$(kore_dir simple)/definition.kore" --runtime "$(kore_dir simple)/runtime.json" \
            --out "$o" --name KSimple --prelude ../../lean/prelude --linear-terms \
            --open-obligations "$o/open-obligations.txt" ;;
    simple-ar) "$G" gen --kore "$(kore_dir simple)/definition.kore" --runtime "$(kore_dir simple)/runtime.json" \
            --out "$o" --name KSimple --prelude ../../lean/prelude --arity-terms \
            --open-obligations "$o/open-obligations.txt" ;;
    # SIMPLE with the K function `holdsOk` (demos/k/simple-inv): a cell predicate of `<holds>`, which
    # is inside the `<thread>` cell map, so it is lifted to "every thread"
    simpleinv) "$G" gen --kore "$(kore_dir simple-inv)/definition.kore" --runtime "$(kore_dir simple-inv)/runtime.json" \
            --out "$o" --name KSimpleInv --prelude ../../lean/prelude --linear-terms \
            --open-obligations "$o/open-obligations.txt" --invariant holdsOk@holds ;;
    # the same definition with "every store value is a Val or undefined", as a function of the `<store>` cell's
    # content and as a function of SIMPLE's top cell `<T>`
    simplestore|simplet) "$G" gen --kore "$(kore_dir simple-inv)/definition.kore" --runtime "$(kore_dir simple-inv)/runtime.json" \
            --out "$o" --name KSimpleInv --prelude ../../lean/prelude --linear-terms \
            --open-obligations "$o/open-obligations.txt" \
            --invariant "$([ "$1" = simplet ] && echo tStoreOk@T || echo storeOk@store)" ;;
    # the variant of SIMPLE (tests/simple-variant.py), related to SIMPLE by demos/SimpleRel
    simplev) "$G" gen --kore "$(kore_dir simple-variant)/definition.kore" --runtime "$(kore_dir simple-variant)/runtime.json" \
            --out "$o" --name KSimpleV --prelude ../../lean/prelude --linear-terms \
            --open-obligations "$o/open-obligations.txt" ;;
    # the generator's K fixtures (tests/fixtures, compiled KORE checked in): freekey's functions
    # walk maps by free-key patterns; peano and cellmap, each generated twice under two
    # namespaces, are the two sides of the self-relations demos/PeanoRel and demos/CellMapRel
    peano|peanob|cellmap|cellmapb|freekey) local fx; fx=$(libs_fixture "$1")
      "$G" gen --kore "$fx/definition.kore" --runtime "$fx/runtime.json" \
            --out "$o" --name "$(libs_name "$1")" --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt" ;;
    # recursive functions whose termination measures the generator synthesizes (demos/k/term)
    kterm-ar) "$G" gen --kore "$(kore_dir kterm)/definition.kore" --runtime "$(kore_dir kterm)/runtime.json" \
            --out "$o" --name KTerm --prelude ../../lean/prelude --arity-terms \
            --open-obligations "$o/open-obligations.txt" ;;
    *) echo "libs_gen: unknown library $1" >&2; return 2 ;;
  esac
}

# libs_fixture DIR: the fixture directory (tests/fixtures/NAME) of fixture library DIR.
libs_fixture() {
  local n=${1%b}   # peanob, cellmapb: the fixture of peano, cellmap
  echo "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/fixtures/$n"
}

# libs_gen_ill_typed DIR: KRS IMP with an ill-typed `assign` (krs-imp-ill-typed.py beside this file), with
# the sidecar, into DIR (namespace KrsImp, so its Terms.lean equals krsimp's): the generated proof of the
# declared cell type must fail at `KRS-IMP.assign` (the gate's negative check).
libs_gen_ill_typed() {
  python3 -I "$(dirname "${BASH_SOURCE[0]}")/krs-imp-ill-typed.py" "$KRS/definition.kore" "$1/definition.kore" &&
  "$G" gen --kore "$1/definition.kore" --out "$1" --name KrsImp --prelude ../../lean/prelude \
    --open-obligations "$1/open-obligations.txt" --sidecar "$KRS/k2lean-sidecar.json"
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

# libs_relate NS: the relation of demo NS (ImpRel: `Bisim.lean`; ImpTypes, ImpMut: `Tr.lean`, all
# from kimp; SimpleRel: `Bisim.lean`, SIMPLE to its variant; PeanoRel, CellMapRel: `Bisim.lean`, a
# fixture to itself) and its correspondence report.
libs_relate() {
  local ns=$1 na=KImp ka nb kd f=Tr extra=()
  ka=$(kore_dir kimp)
  case $ns in
    ImpRel) nb=KrsImp kd=$KRS f=Bisim ;;
    ImpTypes) nb=KImpTypes kd=$(kore_dir imp-typing) extra=(--roots "SortStmt,SortExpr") ;;
    ImpMut) nb=KMut kd=$(kore_dir kmut) ;;
    SimpleRel) na=KSimple ka=$(kore_dir simple) nb=KSimpleV kd=$(kore_dir simple-variant) f=Bisim ;;
    # a fixture related to itself (libraries peano and peanob, cellmap and cellmapb)
    PeanoRel) na=Peano ka=$(libs_fixture peano) nb=PeanoB kd=$ka f=Bisim ;;
    CellMapRel) na=CellMap ka=$(libs_fixture cellmap) nb=CellMapB kd=$ka f=Bisim ;;
    *) echo "libs_relate: unknown demo $ns" >&2; return 2 ;;
  esac
  # the syntax definitions name the concrete syntax of symbols; the fixtures have none
  local sa=() sb=()
  [ -f "$ka/syntaxDefinition.kore" ] && sa=(--syntax-a "$ka/syntaxDefinition.kore")
  [ -f "$kd/syntaxDefinition.kore" ] && sb=(--syntax-b "$kd/syntaxDefinition.kore")
  "$G" relate --kore-a "$ka/definition.kore" "${sa[@]}" --name-a "$na" \
    --kore-b "$kd/definition.kore" "${sb[@]}" --name-b "$nb" \
    --ns "$ns" "${extra[@]}" --out "$DEMOS/$ns/$ns/$f.lean" --report "$DEMOS/$ns/correspondence.toml"
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
