# shellcheck shell=bash
# The relational area: `relate` (ImpRel, ImpMut with the mutant library kmut, the fixture
# self-relations PeanoRel, CellMapRel and PickRel, SimpleRel outside the gate) and `refine` (ImpUnroll, with
# the library kunroll). Registry: relational.py.

kore_relational() {
  case $1 in
    kmut) f=$DEMOS/k/kimp-mutant/imp.k m=IMP s=IMP-SYNTAX inc=$DEMOS/k/kimp-mutant ;;
    # kimp whose `while` unrolls straight to the two-armed `if` (tests/kimp-unroll.py), the other
    # side of the stuttering bisimulation demos/ImpUnroll
    kimp-unroll) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/kimp-unroll.py" "$KIMP/imp.k" "$2.src/imp.k" || return 2
      f=$2.src/imp.k m=IMP s=IMP-SYNTAX inc=$KIMP ;;
    # SIMPLE written differently (tests/simple-variant.py: constructors with other symbols, rules
    # in another order), the other side of the relation demos/SimpleRel
    simple-variant) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/simple-variant.py" "$SD/simple-untyped.md" "$2.src/simple-variant.md" || return 2
      f=$2.src/simple-variant.md m=SIMPLE-UNTYPED s=SIMPLE-UNTYPED-SYNTAX inc=$SD ;;
    *) return 1 ;;
  esac
}

name_relational() {
  case $1 in
    kmut) echo KMut ;; kunroll) echo KUnroll ;; simplev) echo KSimpleV ;;
    peano) echo Peano ;; peanob) echo PeanoB ;; cellmap) echo CellMap ;; cellmapb) echo CellMapB ;;
    pick) echo Pick ;; pickb) echo PickB ;;
    *) return 1 ;;
  esac
}

gen_relational() {
  case $1 in
    kmut) GEN_ARGS=(--kore "$(kore_dir kmut)/definition.kore" --runtime "$(kore_dir kmut)/runtime.json"
            --out "$o" --name KMut --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt") ;;
    kunroll) GEN_ARGS=(--kore "$(kore_dir kimp-unroll)/definition.kore" --runtime "$(kore_dir kimp-unroll)/runtime.json"
            --out "$o" --name KUnroll --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt") ;;
    # the variant of SIMPLE (tests/simple-variant.py), related to SIMPLE by demos/SimpleRel
    simplev) GEN_ARGS=(--kore "$(kore_dir simple-variant)/definition.kore" --runtime "$(kore_dir simple-variant)/runtime.json"
            --out "$o" --name KSimpleV --prelude ../../lean/prelude --linear-terms
            --open-obligations "$o/open-obligations.txt") ;;
    # the generator's fixtures peano, cellmap and pick, each generated twice under two namespaces:
    # the two sides of the self-relations demos/PeanoRel, demos/CellMapRel and demos/PickRel
    peano|peanob|cellmap|cellmapb|pick|pickb) libs_fixture_args "$1" ;;
    *) return 1 ;;
  esac
  return 0
}

# ImpRel: `Bisim.lean`, kimp to KRS IMP; ImpMut: `Tr.lean`, kimp to its mutant; ImpUnroll: the
# per-rule lemmas that `refine` reads; SimpleRel: `Bisim.lean`, SIMPLE to its variant; PeanoRel,
# CellMapRel, PickRel: `Bisim.lean`, a fixture to itself (libraries peano and peanob, cellmap and
# cellmapb, pick and pickb)
relate_relational() {
  case $1 in
    ImpRel) nb=KrsImp kd=$KRS f=Bisim extra=(--per-sort-terms true) ;;
    ImpMut) nb=KMut kd=$(kore_dir kmut) ;;
    ImpUnroll) nb=KUnroll kd=$(kore_dir kimp-unroll) extra=(--per-rule true) ;;
    SimpleRel) na=KSimple ka=$(kore_dir simple) nb=KSimpleV kd=$(kore_dir simple-variant) f=Bisim extra=(--split true) ;;
    PeanoRel) na=Peano ka=$(libs_fixture peano) nb=PeanoB kd=$ka f=Bisim ;;
    CellMapRel) na=CellMap ka=$(libs_fixture cellmap) nb=CellMapB kd=$ka f=Bisim ;;
    PickRel) na=Pick ka=$(libs_fixture pick) nb=PickB kd=$ka f=Bisim ;;
    *) return 1 ;;
  esac
}

# libs_refine NS: the generated module of the stuttering-bisimulation demo NS after its hand module
# `NS/Relation.lean` (ImpUnroll: kimp against tests/kimp-unroll.py's variant; needs libs_relate NS first,
# whose `--per-rule` lemmas and report it reads), and its report `NS/refine.toml`.
libs_refine() {
  case $1 in
    ImpUnroll) "$G" refine --kore-a "$(kore_dir kimp)/definition.kore" --name-a KImp \
        --kore-b "$(kore_dir kimp-unroll)/definition.kore" --name-b KUnroll --ns ImpUnroll \
        --correspondence "$DEMOS/ImpUnroll/correspondence.toml" --open "$DEMOS/ImpUnroll/open-cases.txt" \
        --out "$DEMOS/ImpUnroll/ImpUnroll/Refine.lean" --report "$DEMOS/ImpUnroll/refine.toml" ;;
    *) echo "libs_refine: unknown demo $1" >&2; return 2 ;;
  esac
}

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

gate_relational() {
  kc kimp
  runs lib kmut && kc kmut && lib kmut KMut
  phase "demos relational"
  runs demo ImpRel && { rel ImpRel; dbuild ImpRel; }
  runs demo ImpMut && kc kmut && { rel ImpMut; dbuild ImpMut; }
  # three fixtures related to themselves: PeanoRel (an `owise` priority, recursive and mutual
  # functions), CellMapRel (a free-key rule over a typed cell map) and PickRel (functions with
  # free-key map patterns); each side generated under its own namespace and built only as far as
  # the relation needs (Rules)
  local d
  if runs demo PeanoRel; then
    for d in peano peanob; do partlib "$d" "$(libs_name "$d").Rules"; done
    rel PeanoRel; dbuild PeanoRel
  fi
  if runs demo CellMapRel; then
    for d in cellmap cellmapb; do partlib "$d" "$(libs_name "$d").Rules"; done
    rel CellMapRel; dbuild CellMapRel
  fi
  if runs demo PickRel; then
    for d in pick pickb; do partlib "$d" "$(libs_name "$d").Rules"; done
    rel PickRel; dbuild PickRel
  fi
  # a stuttering bisimulation (docs/design.md, section 3.5): kimp against tests/kimp-unroll.py's
  # variant, library kunroll built only as far as the demo needs
  if runs demo ImpUnroll; then
    phase "scaffold ImpUnroll"
    kc kimp-unroll && partlib kunroll KUnroll.Preserves
    rel ImpUnroll
    scaffold refine-ImpUnroll libs_refine ImpUnroll
    dbuild ImpUnroll
  fi
  phase "diff relational"
  diffs kmut
}
