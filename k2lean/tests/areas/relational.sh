# shellcheck shell=bash
# The relational area: `relate` (ImpRel, ImpMut with the mutant library kmut, the fixture
# self-relations PeanoRel, CellMapRel and PickRel, SimpleRel outside the gate) and `refine` (ImpUnroll, with
# the library kunroll; with priority ranks, VmPopRefine, libraries vmpop and vmpop1, and ImpPrintRefine,
# libraries kprint and kprintu; refuted by two runs, ImpUnrollMut and VmPopMut, libraries kunrollle and
# vmpop1skip; under a legality, VmEmptyRefine, RangeIncRefine and VmEmptyMut, libraries vmempty,
# vmemptyopt, vmemptystale, rangeinc and rangeincopt, and VmPopLegal, library vmpopinv). Registry:
# relational.py.

kore_relational() {
  case $1 in
    kmut) f=$DEMOS/k/kimp-mutant/imp.k m=IMP s=IMP-SYNTAX inc=$DEMOS/k/kimp-mutant ;;
    # kimp whose `while` unrolls straight to the two-armed `if` (tests/kimp-unroll.py), the other
    # side of the stuttering bisimulation demos/ImpUnroll
    kimp-unroll) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/kimp-unroll.py" "$KIMP/imp.k" "$2.src/imp.k" || return 2
      f=$2.src/imp.k m=IMP s=IMP-SYNTAX inc=$KIMP ;;
    # kimp with `print` to K's stdout stream (tests/kimp-print.py: the stream's rules at priorities
    # 25 and 30), and the same with tests/kimp-unroll.py's `while`: the sides of demos/ImpPrintRefine
    kimp-print) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/kimp-print.py" "$KIMP" "$2.src" || return 2
      f=$2.src/imp.k m=IMP s=IMP-SYNTAX inc=$2.src ;;
    kimp-print-unroll) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/kimp-print.py" "$KIMP" "$2.src" &&
      python3 -I "$LIBS_DIR/kimp-unroll.py" "$2.src/imp.k" "$2.src/imp.k" || return 2
      f=$2.src/imp.k m=IMP s=IMP-SYNTAX inc=$2.src ;;
    # tests/kimp-unroll.py's variant with `<=` read as `<` (tests/refine-mutant.py imp-le): the other
    # side of demos/ImpUnrollMut, against kimp
    kimp-unroll-le) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/refine-mutant.py" imp-le "$KIMP" "$2.src" &&
      python3 -I "$LIBS_DIR/kimp-unroll.py" "$2.src/imp.k" "$2.src/imp.k" || return 2
      f=$2.src/imp.k m=IMP s=IMP-SYNTAX inc=$2.src ;;
    # the fixture vmpop compiled whole, so that krust runs it (the witnesses' initial configurations
    # of demos/VmPopMut, `rel_witnesses`), and vmpop1 whose `pop` on an empty stack does nothing
    # (tests/refine-mutant.py vm-pop-skip), the other side of demos/VmPopMut
    vmpop-run) f=$FIXTURES/vmpop/vmpop.k m=VMPOP s=VMPOP-SYNTAX inc=$FIXTURES/vmpop ;;
    vmpop1-skip) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/refine-mutant.py" vm-pop-skip "$FIXTURES/vmpop1/vmpop1.k" "$2.src/vmpop1.k" || return 2
      f=$2.src/vmpop1.k m=VMPOP1 s=VMPOP1-SYNTAX inc=$2.src ;;
    # vmpri with a cache `<empty>` of whether the stack is empty, and the same whose underflow rules
    # read the cache (tests/refine-mutant.py vm-empty, vm-empty-opt): the sides of demos/VmEmptyRefine;
    # and the same whose `pop-last` leaves the cache stale (vm-empty-stale), the other side of
    # demos/VmEmptyMut
    vm-empty|vm-empty-opt|vm-empty-stale) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/refine-mutant.py" "$1" "$FIXTURES/vmpri/vmpri.k" "$2.src/vmpri.k" || return 2
      f=$2.src/vmpri.k m=VMPRI s=VMPRI-SYNTAX inc=$2.src ;;
    # range with `inc(L)`, with and without its check that the value is nonnegative
    # (tests/refine-mutant.py range-inc, range-inc-opt): the sides of demos/RangeIncRefine
    range-inc|range-inc-opt) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/refine-mutant.py" "$1" "$FIXTURES/range/range.k" "$2.src/range.k" || return 2
      f=$2.src/range.k m=RANGE s=RANGE-SYNTAX inc=$2.src ;;
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
    kprint) echo KImpPrint ;; kprintu) echo KImpPrintU ;;
    peano) echo Peano ;; peanob) echo PeanoB ;; cellmap) echo CellMap ;; cellmapb) echo CellMapB ;;
    pick) echo Pick ;; pickb) echo PickB ;; vmpop) echo KVmPop ;; vmpop1) echo KVmPop1 ;;
    kunrollle) echo KUnrollLe ;; vmpop1skip) echo KVmPop1Skip ;;
    vmempty) echo KVmEmpty ;; vmemptyopt) echo KVmEmptyOpt ;; vmemptystale) echo KVmEmptyStale ;;
    rangeinc) echo KRangeInc ;; rangeincopt) echo KRangeIncOpt ;; vmpopinv) echo KVmPopInv ;;
    *) return 1 ;;
  esac
}

gen_relational() {
  case $1 in
    kmut) GEN_ARGS=(--kore "$(kore_dir kmut)/definition.kore" --runtime "$(kore_dir kmut)/runtime.json"
            --out "$o" --name KMut --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    kunroll) GEN_ARGS=(--kore "$(kore_dir kimp-unroll)/definition.kore" --runtime "$(kore_dir kimp-unroll)/runtime.json"
            --out "$o" --name KUnroll --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    # the mutants of the refine demos' second sides (tests/refine-mutant.py): demos/ImpUnrollMut and
    # demos/VmPopMut
    kunrollle|vmpop1skip) local k=kimp-unroll-le; [ "$1" = vmpop1skip ] && k=vmpop1-skip
      GEN_ARGS=(--kore "$(kore_dir $k)/definition.kore" --runtime "$(kore_dir $k)/runtime.json"
            --out "$o" --name "$(libs_name "$1")" --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    # the sides of demos/VmEmptyRefine; the first with its invariant, the cache is right (`emptyOk`),
    # which `refine --assume-invariant` reads
    vmempty) GEN_ARGS=(--kore "$(kore_dir vm-empty)/definition.kore" --runtime "$(kore_dir vm-empty)/runtime.json"
            --out "$o" --name KVmEmpty --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant emptyOk@T) ;;
    vmemptyopt|vmemptystale) local k=vm-empty-opt; [ "$1" = vmemptystale ] && k=vm-empty-stale
      GEN_ARGS=(--kore "$(kore_dir $k)/definition.kore" --runtime "$(kore_dir $k)/runtime.json"
            --out "$o" --name "$(libs_name "$1")" --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    # the fixture vmpop with its invariant (`kOk`, every item of `<k>` an instruction, a program or a
    # halt), the first side of demos/VmPopLegal
    vmpopinv) local fx; fx=$(libs_fixture vmpop)
      GEN_ARGS=(--kore "$fx/definition.kore" --runtime "$fx/runtime.json"
            --out "$o" --name KVmPopInv --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant kOk@k) ;;
    # the sides of demos/RangeIncRefine; the first with the fixture's invariant (`storeNat`)
    rangeinc) GEN_ARGS=(--kore "$(kore_dir range-inc)/definition.kore" --runtime "$(kore_dir range-inc)/runtime.json"
            --out "$o" --name KRangeInc --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant storeNat@store) ;;
    rangeincopt) GEN_ARGS=(--kore "$(kore_dir range-inc-opt)/definition.kore" --runtime "$(kore_dir range-inc-opt)/runtime.json"
            --out "$o" --name KRangeIncOpt --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    kprint|kprintu) local k=kimp-print; [ "$1" = kprintu ] && k=kimp-print-unroll
      GEN_ARGS=(--kore "$(kore_dir $k)/definition.kore" --runtime "$(kore_dir $k)/runtime.json"
            --out "$o" --name "$(libs_name "$1")" --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    # the variant of SIMPLE (tests/simple-variant.py), related to SIMPLE by demos/SimpleRel
    simplev) GEN_ARGS=(--kore "$(kore_dir simple-variant)/definition.kore" --runtime "$(kore_dir simple-variant)/runtime.json"
            --out "$o" --name KSimpleV --prelude ../../lean
            --open-obligations "$o/open-obligations.txt") ;;
    # the generator's fixtures peano, cellmap and pick, each generated twice under two namespaces:
    # the two sides of the self-relations demos/PeanoRel, demos/CellMapRel and demos/PickRel
    peano|peanob|cellmap|cellmapb|pick|pickb) libs_fixture_args "$1" ;;
    # the fixtures vmpop (`pop` in two steps) and vmpop1 (in one), the two sides of the stuttering
    # bisimulation demos/VmPopRefine, with vmpri's priority ranks
    vmpop|vmpop1) libs_fixture_args "$1" ;;
    *) return 1 ;;
  esac
  return 0
}

# ImpRel: `Bisim.lean`, kimp to KRS IMP; ImpMut: `Tr.lean`, kimp to its mutant; ImpUnroll and
# VmPopRefine: the per-rule lemmas that `refine` reads; SimpleRel: `Bisim.lean`, SIMPLE to its variant; PeanoRel,
# CellMapRel, PickRel: `Bisim.lean`, a fixture to itself (libraries peano and peanob, cellmap and
# cellmapb, pick and pickb)
relate_relational() {
  case $1 in
    ImpRel) nb=KrsImp kd=$KRS f=Bisim ;;
    ImpMut) nb=KMut kd=$(kore_dir kmut) ;;
    ImpUnroll) nb=KUnroll kd=$(kore_dir kimp-unroll) extra=(--per-rule true) ;;
    ImpPrintRefine) na=KImpPrint ka=$(kore_dir kimp-print) nb=KImpPrintU kd=$(kore_dir kimp-print-unroll) extra=(--per-rule true) ;;
    VmPopRefine) na=KVmPop ka=$(libs_fixture vmpop) nb=KVmPop1 kd=$(libs_fixture vmpop1) extra=(--per-rule true) ;;
    ImpUnrollMut) nb=KUnrollLe kd=$(kore_dir kimp-unroll-le) extra=(--per-rule true) ;;
    VmPopMut) na=KVmPop ka=$(libs_fixture vmpop) nb=KVmPop1Skip kd=$(kore_dir vmpop1-skip) extra=(--per-rule true) ;;
    VmEmptyRefine) na=KVmEmpty ka=$(kore_dir vm-empty) nb=KVmEmptyOpt kd=$(kore_dir vm-empty-opt) extra=(--per-rule true) ;;
    VmPopLegal) na=KVmPopInv ka=$(libs_fixture vmpop) nb=KVmPop1 kd=$(libs_fixture vmpop1) extra=(--per-rule true) ;;
    VmEmptyMut) na=KVmEmpty ka=$(kore_dir vm-empty) nb=KVmEmptyStale kd=$(kore_dir vm-empty-stale) extra=(--per-rule true) ;;
    RangeIncRefine) na=KRangeInc ka=$(kore_dir range-inc) nb=KRangeIncOpt kd=$(kore_dir range-inc-opt) extra=(--per-rule true) ;;
    SimpleRel) na=KSimple ka=$(kore_dir simple) nb=KSimpleV kd=$(kore_dir simple-variant) f=Bisim extra=(--split true) ;;
    PeanoRel) na=Peano ka=$(libs_fixture peano) nb=PeanoB kd=$ka f=Bisim ;;
    CellMapRel) na=CellMap ka=$(libs_fixture cellmap) nb=CellMapB kd=$ka f=Bisim ;;
    PickRel) na=Pick ka=$(libs_fixture pick) nb=PickB kd=$ka f=Bisim ;;
    *) return 1 ;;
  esac
}

# libs_refine NS: the generated module of the stuttering-bisimulation demo NS and its report
# `NS/refine.toml` (ImpUnroll: kimp against tests/kimp-unroll.py's variant, with no hand module, `X`
# generated from the split of `while`; VmPopRefine: the fixture vmpop against vmpop1, `X` from the
# split of `pop`, with priority ranks; ImpPrintRefine: ImpUnroll's split with K's stdout stream
# rules before it; needs libs_relate NS first, whose `--per-rule` lemmas and
# report it reads).
libs_refine() {
  case $1 in
    ImpUnroll) "$G" refine --kore-a "$(kore_dir kimp)/definition.kore" --name-a KImp \
        --kore-b "$(kore_dir kimp-unroll)/definition.kore" --name-b KUnroll --ns ImpUnroll \
        --correspondence "$DEMOS/ImpUnroll/correspondence.toml" --hand-module none \
        --out "$DEMOS/ImpUnroll/ImpUnroll/Refine.lean" --report "$DEMOS/ImpUnroll/refine.toml" ;;
    ImpPrintRefine) "$G" refine --kore-a "$(kore_dir kimp-print)/definition.kore" --name-a KImpPrint \
        --kore-b "$(kore_dir kimp-print-unroll)/definition.kore" --name-b KImpPrintU --ns ImpPrintRefine \
        --correspondence "$DEMOS/ImpPrintRefine/correspondence.toml" --hand-module none \
        --out "$DEMOS/ImpPrintRefine/ImpPrintRefine/Refine.lean" --report "$DEMOS/ImpPrintRefine/refine.toml" ;;
    VmPopRefine) "$G" refine --kore-a "$(libs_fixture vmpop)/definition.kore" --name-a KVmPop \
        --kore-b "$(libs_fixture vmpop1)/definition.kore" --name-b KVmPop1 --ns VmPopRefine \
        --correspondence "$DEMOS/VmPopRefine/correspondence.toml" --hand-module none \
        --out "$DEMOS/VmPopRefine/VmPopRefine/Refine.lean" --report "$DEMOS/VmPopRefine/refine.toml" ;;
    # under a legality: vmpri with a cache, against the same whose underflow rules read it
    # (tests/refine-mutant.py vm-empty, vm-empty-opt), under the invariant that the cache is right;
    # the underflow rules' parts by hand (NS/Hand.lean, listed in NS/open.txt)
    VmEmptyRefine) "$G" refine --kore-a "$(kore_dir vm-empty)/definition.kore" --name-a KVmEmpty \
        --kore-b "$(kore_dir vm-empty-opt)/definition.kore" --name-b KVmEmptyOpt --ns VmEmptyRefine \
        --correspondence "$DEMOS/VmEmptyRefine/correspondence.toml" --open "$DEMOS/VmEmptyRefine/open.txt" \
        --hand-module VmEmptyRefine.Hand --assume-invariant KVmEmpty.Invariant \
        --out "$DEMOS/VmEmptyRefine/VmEmptyRefine/Refine.lean" --report "$DEMOS/VmEmptyRefine/refine.toml" ;;
    # VmPopRefine's split under vmpop's invariant (`kOk`): the legality threaded through the split's
    # parts (`split_bwd`, and `A`'s state after `X_next` by the invariant's preservation)
    VmPopLegal) "$G" refine --kore-a "$(libs_fixture vmpop)/definition.kore" --name-a KVmPopInv \
        --kore-b "$(libs_fixture vmpop1)/definition.kore" --name-b KVmPop1 --ns VmPopLegal \
        --correspondence "$DEMOS/VmPopLegal/correspondence.toml" --hand-module none \
        --assume-invariant KVmPopInv.Invariant \
        --out "$DEMOS/VmPopLegal/VmPopLegal/Refine.lean" --report "$DEMOS/VmPopLegal/refine.toml" ;;
    # a wrong optimization under the legality: the cache left stale by `pop-last`
    # (tests/refine-mutant.py vm-empty-stale); the rules that differ have their parts open
    # (NS/open.txt), refuted together by a program's runs from an initial configuration, which
    # satisfies the invariant (`witness.NAME.legal`; rel_witnesses first)
    VmEmptyMut) "$G" refine --kore-a "$(kore_dir vm-empty)/definition.kore" --name-a KVmEmpty \
        --kore-b "$(kore_dir vm-empty-stale)/definition.kore" --name-b KVmEmptyStale --ns VmEmptyMut \
        --correspondence "$DEMOS/VmEmptyMut/correspondence.toml" --open "$DEMOS/VmEmptyMut/open.txt" \
        --hand-module none --assume-invariant KVmEmpty.Invariant --witnesses "$DEMOS/VmEmptyMut/witnesses" \
        --out "$DEMOS/VmEmptyMut/VmEmptyMut/Refine.lean" --report "$DEMOS/VmEmptyMut/refine.toml" ;;
    # a check the invariant makes redundant: range's `inc`, and the same without its check
    # (tests/refine-mutant.py range-inc, range-inc-opt), under the fixture's invariant (`storeNat`)
    RangeIncRefine) "$G" refine --kore-a "$(kore_dir range-inc)/definition.kore" --name-a KRangeInc \
        --kore-b "$(kore_dir range-inc-opt)/definition.kore" --name-b KRangeIncOpt --ns RangeIncRefine \
        --correspondence "$DEMOS/RangeIncRefine/correspondence.toml" --open "$DEMOS/RangeIncRefine/open.txt" \
        --hand-module RangeIncRefine.Hand --assume-invariant KRangeInc.Invariant \
        --out "$DEMOS/RangeIncRefine/RangeIncRefine/Refine.lean" --report "$DEMOS/RangeIncRefine/refine.toml" ;;
    # the two mutants (tests/refine-mutant.py): the mutated rule's parts open (NS/open.txt), refuted
    # together by the witnesses' runs (`--witnesses`, NS/Witnesses.lean; rel_witnesses first)
    ImpUnrollMut) "$G" refine --kore-a "$(kore_dir kimp)/definition.kore" --name-a KImp \
        --kore-b "$(kore_dir kimp-unroll-le)/definition.kore" --name-b KUnrollLe --ns ImpUnrollMut \
        --correspondence "$DEMOS/ImpUnrollMut/correspondence.toml" --hand-module none \
        --open "$DEMOS/ImpUnrollMut/open.txt" --witnesses "$DEMOS/ImpUnrollMut/witnesses" \
        --out "$DEMOS/ImpUnrollMut/ImpUnrollMut/Refine.lean" --report "$DEMOS/ImpUnrollMut/refine.toml" ;;
    VmPopMut) "$G" refine --kore-a "$(libs_fixture vmpop)/definition.kore" --name-a KVmPop \
        --kore-b "$(kore_dir vmpop1-skip)/definition.kore" --name-b KVmPop1Skip --ns VmPopMut \
        --correspondence "$DEMOS/VmPopMut/correspondence.toml" --hand-module none \
        --open "$DEMOS/VmPopMut/open.txt" --witnesses "$DEMOS/VmPopMut/witnesses" \
        --out "$DEMOS/VmPopMut/VmPopMut/Refine.lean" --report "$DEMOS/VmPopMut/refine.toml" ;;
    *) echo "libs_refine: unknown demo $1" >&2; return 2 ;;
  esac
}

# rel_witnesses DIR KORE: the initial configuration NAME.kore of each witness program DIR/NAME.EXT of
# a refine demo (`refine --witnesses`): krust's `krun --depth 0` of the program in definition KORE
# (a krust kcompile directory) with the configuration variables of NAME.vars (one VAR=VALUE a line,
# if any), parsed at the sort of `$PGM`.
rel_witnesses() {
  local p n sort a
  sort=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["configuration_variables"]["PGM"])' "$2/runtime.json") || return 2
  for p in "$1"/*; do
    case $p in *.kore | *.vars | *'*') continue ;; esac
    n=${p%.*}
    a=()
    if [ -f "$n.vars" ]; then
      while IFS= read -r l; do [ -n "$l" ] && a+=(-c "$l"); done < "$n.vars"
    fi
    "$KRUST" krun --definition "$2" --depth 0 --sort "$sort" "${a[@]}" "$p" > "$n.kore" < /dev/null || return 2
  done
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
  # variant, library kunroll built only as far as the demo needs; each refine demo's parts are read
  # by name from its built environment (dbuild_slots)
  if runs demo ImpUnroll; then
    phase "scaffold ImpUnroll"
    kc kimp-unroll && partlib kunroll KUnroll.Preserves
    rel ImpUnroll
    scaffold refine-ImpUnroll libs_refine ImpUnroll
    dbuild_slots ImpUnroll
  fi
  # the same with priority ranks (vmpri's three): the fixture vmpop, whose `pop` takes two steps,
  # against vmpop1, which takes one; the libraries built as far as the demo needs (Preserves)
  if runs demo VmPopRefine; then
    phase "scaffold VmPopRefine"
    for d in vmpop vmpop1; do partlib "$d" "$(libs_name "$d").Preserves"; done
    rel VmPopRefine
    scaffold refine-VmPopRefine libs_refine VmPopRefine
    dbuild_slots VmPopRefine
  fi
  # ImpUnroll's split under K's stdout stream rules (ranks 0 and 1, before kimp's rules): kimp with
  # `print` (tests/kimp-print.py) against the same with tests/kimp-unroll.py's `while`
  if runs demo ImpPrintRefine; then
    phase "scaffold ImpPrintRefine"
    kc kimp-print && kc kimp-print-unroll && for d in kprint kprintu; do partlib "$d" "$(libs_name "$d").Preserves"; done
    rel ImpPrintRefine
    scaffold refine-ImpPrintRefine libs_refine ImpPrintRefine
    dbuild_slots ImpPrintRefine
  fi
  # refutations by two runs (REL-7): kimp against the unrolled variant with `<=` read as `<`, and
  # vmpop against vmpop1 whose `pop` on an empty stack does nothing (tests/refine-mutant.py); the
  # mutated rules' parts open, and a program on which the two disagree refutes them (`Open.refuted`)
  if runs demo ImpUnrollMut; then
    phase "scaffold ImpUnrollMut"
    kc kimp-unroll-le && partlib kunrollle KUnrollLe.Adequacy
    rel ImpUnrollMut
    scaffold witnesses-ImpUnrollMut rel_witnesses "$DEMOS/ImpUnrollMut/witnesses" "$(kore_dir kimp)"
    scaffold refine-ImpUnrollMut libs_refine ImpUnrollMut
    dbuild_slots ImpUnrollMut
  fi
  if runs demo VmPopMut; then
    phase "scaffold VmPopMut"
    kc vmpop-run && kc vmpop1-skip && partlib vmpop KVmPop.Adequacy && partlib vmpop1skip KVmPop1Skip.Adequacy
    rel VmPopMut
    scaffold witnesses-VmPopMut rel_witnesses "$DEMOS/VmPopMut/witnesses" "$(kore_dir vmpop-run)"
    scaffold refine-VmPopMut libs_refine VmPopMut
    dbuild_slots VmPopMut
  fi
  # under a legality (REL-8): vmpri with a cache against the same whose underflow rules read it,
  # and range's `inc` against the same without its check, each under the first side's invariant
  # (`gen --invariant`, the cache is right; every stored value is nonnegative), the parts that need
  # it by hand (NS/Hand.lean); and the cache left stale by `pop-last`, refuted by a program from an
  # initial configuration, which satisfies the invariant
  if runs demo VmEmptyRefine; then
    phase "scaffold VmEmptyRefine"
    kc vm-empty && kc vm-empty-opt && partlib vmempty KVmEmpty.Invariants && partlib vmemptyopt KVmEmptyOpt.Preserves
    rel VmEmptyRefine
    scaffold refine-VmEmptyRefine libs_refine VmEmptyRefine
    dbuild_slots VmEmptyRefine
  fi
  if runs demo RangeIncRefine; then
    phase "scaffold RangeIncRefine"
    kc range-inc && kc range-inc-opt && partlib rangeinc KRangeInc.Invariants && partlib rangeincopt KRangeIncOpt.Preserves
    rel RangeIncRefine
    scaffold refine-RangeIncRefine libs_refine RangeIncRefine
    dbuild_slots RangeIncRefine
  fi
  if runs demo VmPopLegal; then
    phase "scaffold VmPopLegal"
    partlib vmpopinv KVmPopInv.Invariants && partlib vmpop1 KVmPop1.Preserves
    rel VmPopLegal
    scaffold refine-VmPopLegal libs_refine VmPopLegal
    dbuild_slots VmPopLegal
  fi
  if runs demo VmEmptyMut; then
    phase "scaffold VmEmptyMut"
    kc vm-empty && kc vm-empty-stale && partlib vmempty KVmEmpty.Invariants && partlib vmemptystale KVmEmptyStale.Adequacy
    rel VmEmptyMut
    scaffold witnesses-VmEmptyMut rel_witnesses "$DEMOS/VmEmptyMut/witnesses" "$(kore_dir vm-empty)"
    scaffold refine-VmEmptyMut libs_refine VmEmptyMut
    dbuild_slots VmEmptyMut
  fi
  phase "diff relational"
  diffs kmut
}
