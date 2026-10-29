# shellcheck shell=bash
# The soundness area: `soundness` (ImpTypes: kimp against the type checker demos/k/imp-typing.k,
# library imptypes; ExprTypes: kimp's expression language EXPR against demos/k/expr-typing.k,
# libraries kexpr and exprtypes; ImpPlusTypes: IMP++ of K's tutorial, whose threads are a cell map,
# against demos/k/impplus-typing.k, libraries impplus and impplustypes), and no stuck states
# (`gen --progress`: the stack machine tests/fixtures/vm, library vm, and its variant without a rule,
# tests/fixtures/vmstuck, library vmstuck, whose one stuck case is refuted by hand, and its variant
# with priorities, tests/fixtures/vmpri, library vmpri; coroutines in a
# cell map, tests/fixtures/coro, library coro, and its variant with a join that can deadlock,
# tests/fixtures/corojoin, library corojoin, whose deadlock is refuted by hand; a coordination
# script's tasks, tests/fixtures/handoff, under the kind 2 invariant of demos/HandoffConf; and each
# typed language under its runtime typing, kimp in demos/ImpTypes, EXPR in demos/ExprTypes and IMP++
# in demos/ImpPlusTypes, whose generated Soundness.lean derives type soundness from it).
# Registry: soundness.py.

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
    vm) echo KVm ;;
    vmstuck) echo KVmStuck ;;
    vmpri) echo KVmPri ;;
    coro) echo Coro ;;
    corojoin) echo CoroJoin ;;
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
    # no stuck states: the machine's well-formedness `kOk` (only instructions, programs and halts on
    # `<k>`), its acceptable endings `halted`
    vm|vmstuck|vmpri) libs_fixture_args "$1"; GEN_ARGS+=(--invariant kOk@k --progress --ending halted@k) ;;
    coro|corojoin) libs_fixture_args "$1"; GEN_ARGS+=(--invariant kOk@k --progress --ending ended@k) ;;
    *) return 1 ;;
  esac
  return 0
}

# no stuck states: `{ns}/Progress.lean`. A case that `k2l_progress` does not close becomes an open
# case (`open-from-log` into open-progress-cases.txt) and the library is regenerated, so the case is
# then taken from the hand module (proved, or refuted: a third outcome of `progress`, `Progress.Refuted`),
# as for invariants.
progcases() { # DIR NAME: build NAME.Progress, at most three attempts; the last log is build-DIR-prog.log
  local d=$1 n=$2 o=$GEN/$1 k
  for k in 1 2 3; do
    if lbuild "$o" "build-$d-prog-$k" "$n.Progress"; then
      cp "$L/build-$d-prog-$k.log" "$L/build-$d-prog.log"; ok "progress $d" "$L/build-$d-prog.log"; return 0
    fi
    cp "$L/build-$d-prog-$k.log" "$L/build-$d-prog.log"
    [ "$k" = 3 ] && break
    "$G" open-from-log "$o/$n/Progress.lean" "$L/build-$d-prog-$k.log" "$o/open-progress-cases.txt" >> "$L/gen-$d.log" 2>&1
    genlib "$d" >> "$L/gen-$d.log" 2>&1 || { bad "gen $d" "$L/gen-$d.log"; return 1; }
  done
  bad "progress $d" "$L/build-$d-prog.log"; unbuilt "$o" "$L/build-$d-prog.log" "$n.Progress"; return 1
}
prog_reset() { # DIR: GATE_RETRY_OPEN also retries the open progress cases (refuted ones are kept)
  if [ "${GATE_RETRY_OPEN:-0}" = 1 ] && [ -f "$GEN/$1/open-progress-cases.txt" ]; then
    grep -E '^#| \| refuted( hand)?( *#.*)?$' "$GEN/$1/open-progress-cases.txt" > "$GEN/$1/open-progress-cases.txt.keep" || true
    mv -f "$GEN/$1/open-progress-cases.txt.keep" "$GEN/$1/open-progress-cases.txt"
  fi
  return 0
}
# no stuck states under a kind 2 invariant (SND-14 slice 2b): `progress` of the fixture handoff under
# the script's closure `HandoffConf.Live`, which the library cannot import, so the progress modules go
# to the demo that holds it (`--progress-out`); its open cases are proved in HandoffConf/ProgressHand.lean
gen_handoff_prog() {
  local o=$GEN/handoff c=$D/HandoffConf GEN_ARGS=()
  libs_fixture_args handoff
  # the library's kind 1 invariant `wf` (the confluence area's), which `Live` reads
  "$G" gen "${GEN_ARGS[@]}" --invariant wf@T --progress --assume-invariant HandoffConf.Live \
    --invariant-module HandoffConf.Live --invariant-preserved HandoffConf.Live.preserved \
    --invariant-unfold "$c/live-unfold.txt" --element-fact HandoffConf.Live.taskOk \
    --rank HandoffConf.taskRank --progress-out "$c" --progress-prefix HandoffConf
}
prog_handoff() { lib_open handoff; prog_demo handoff "$D/HandoffConf" HandoffConf gen_handoff_prog HandoffConf.Progress; }
# type soundness as an instance (SND-16 to SND-18): `progress` of each typed language under its
# runtime typing `NS.Typed` (the typing `soundness` generates, NS/Typed.lean), with the ending `kDone`
# and the unfolding list that `soundness` writes too; the semantics' library is another entry's, so
# `gen` writes its library to a scratch directory and only the progress modules count; the demo's
# generated Soundness.lean derives `soundness`'s theorem from `no_stuck`
gen_typed_prog() { # NS KORE NAME [ARG…]: the progress modules of KORE's library NAME, into demos/NS
  local ns=$1 k=$2 n=$3 c=$D/$1 o=$GEN/.${1,,}-prog
  shift 3
  "$G" gen --kore "$(kore_dir "$k")/definition.kore" --runtime "$(kore_dir "$k")/runtime.json" \
    --out "$o" --name "$n" --prelude ../../lean --open-obligations "$o/open-obligations.txt" \
    --progress --assume-invariant "$ns.Typed" --invariant-module "$ns.Typed" \
    --invariant-preserved "$ns.Typed.preserved" --invariant-unfold "$c/typed-unfold.txt" \
    --ending-lean "$ns.kDone@k" --progress-out "$c" --progress-prefix "$ns" "$@"
}
# kimp: `var` reads the store, which `envTy` (ImpTypes/Store.lean) types, so it is proved by hand
gen_imptypes_prog() { gen_typed_prog ImpTypes kimp KImp; }
prog_imptypes() { prog_demo imptypes "$D/ImpTypes" ImpTypes gen_imptypes_prog ImpTypes.Soundness; }
# EXPR, whose programs end with a value: `kDone` accepts one value left on `<k>`
gen_exprtypes_prog() { gen_typed_prog ExprTypes expr KExpr; }
prog_exprtypes() { prog_demo exprtypes "$D/ExprTypes" ExprTypes gen_exprtypes_prog ExprTypes.Soundness; }
# IMP++: `<k>` in the cell map `<threads>`, each thread's typing as the element fact, and `kDone` a
# thread finished or waiting at `join(T);` (which no typing excludes: `join(0);` waits on itself)
gen_impplustypes_prog() { gen_typed_prog ImpPlusTypes impplus KImpPlus --element-fact ImpPlusTypes.Typed.thread; }
prog_impplustypes() { prog_demo impplustypes "$D/ImpPlusTypes" ImpPlusTypes gen_impplustypes_prog ImpPlusTypes.Soundness; }
prog_demo() { # NAME DIR PFX GEN TARGET: `progress` written into the demo DIR (`--progress-out DIR
  # --progress-prefix PFX`) by the function GEN and built as far as TARGET, as progcases does for a
  # library: up to three builds, each failed case added to the open list in between
  local n=$1 c=$2 p=$3 gf=$4 t=$5 k
  phase "progress $n"
  if [ "${GATE_RETRY_OPEN:-0}" = 1 ] && [ -f "$c/open-progress-cases.txt" ]; then
    grep -E '^#| \| refuted( hand)?( *#.*)?$' "$c/open-progress-cases.txt" > "$c/open-progress-cases.txt.keep" || true
    mv -f "$c/open-progress-cases.txt.keep" "$c/open-progress-cases.txt"
  fi
  "$gf" > "$L/gen-$n-prog.log" 2>&1 || { bad "gen $n" "$L/gen-$n-prog.log"; return 1; }
  for k in 1 2 3; do
    if lbuild "$c" "build-$n-prog-$k" "$t"; then
      cp "$L/build-$n-prog-$k.log" "$L/build-$n-prog.log"; ok "progress $n" "$L/build-$n-prog.log"; return 0
    fi
    cp "$L/build-$n-prog-$k.log" "$L/build-$n-prog.log"
    [ "$k" = 3 ] && break
    "$G" open-from-log "$c/$p/Progress.lean" "$L/build-$n-prog-$k.log" "$c/open-progress-cases.txt" >> "$L/gen-$n-prog.log" 2>&1
    "$gf" >> "$L/gen-$n-prog.log" 2>&1 || { bad "gen $n" "$L/gen-$n-prog.log"; return 1; }
  done
  bad "progress $n" "$L/build-$n-prog.log"; unbuilt "$c" "$L/build-$n-prog.log" "$t"; return 1
}

prog_lib() { # DIR NAME: a library built as far as `progress` needs: Equations, Invariants, Progress
  local d=$1 n=$2
  phase "lib $d"
  lib_open "$d"
  inv_reset "$d"
  prog_reset "$d"
  if genlib "$d"; then
    eqns "$d" "$n" && invcases "$d" "$n" && progcases "$d" "$n"
  else bad "gen $d" "$L/gen-$d.log"; fi
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
# `NS/Store.lean` (`Typing.lean` before it, `Typed.lean` after it, and `Soundness.lean` after the
# progress modules, with the list `typed-unfold.txt` they unfold; ImpTypes: kimp against the type
# checker demos/k/imp-typing.k, whose store cell <env> the hand module types by `envTy`).
libs_soundness() {
  local d=$DEMOS/$1
  local outs=(--out-typing "$d/$1/Typing.lean" --out-typed "$d/$1/Typed.lean"
              --out-soundness "$d/$1/Soundness.lean" --out-unfold "$d/typed-unfold.txt")
  case $1 in
    ImpTypes) "$G" soundness --kore-a "$(kore_dir kimp)/definition.kore" --name-a KImp \
        --kore-b "$(kore_dir imp-typing)/definition.kore" --name-b KImpTypes --ns ImpTypes \
        --typing typeOf,wt --store-cell env --store-typing envTy \
        "${outs[@]}" ;;
    # programs end with a value and no cell is typed by hand: `typeOf` accepts them (design.md, §3.3)
    ExprTypes) "$G" soundness --kore-a "$(kore_dir expr)/definition.kore" --name-a KExpr \
        --kore-b "$(kore_dir expr-typing)/definition.kore" --name-b KExprTypes --ns ExprTypes \
        --typing typeOf \
        "${outs[@]}" ;;
    # threads in a cell map, holes of two sorts, rules of three ranks (K's I/O streams); the
    # checker types statements without variables (`wt`, `wts`, accepting programs) and calls
    # `printable` on `print`'s arguments; a block's saved environment is an item of `<k>`
    ImpPlusTypes) "$G" soundness --kore-a "$(kore_dir impplus)/definition.kore" --name-a KImpPlus \
        --kore-b "$(kore_dir impplus-typing)/definition.kore" --name-b KImpPlusTypes --ns ImpPlusTypes \
        --typing typeOf,typeOfB,wt,wts --aux printable --program wts --env-item Map \
        "${outs[@]}" ;;
    *) echo "libs_soundness: unknown demo $1" >&2; return 2 ;;
  esac
}

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

gate_soundness() {
  kc kimp
  runs lib imptypes && kc imp-typing && lib imptypes KImpTypes
  # a typed demo: its typing and preservation, its language's progress under the typing, and
  # `soundness` from both (the demo's build needs the progress modules)
  if runs demo ImpTypes; then
    phase "demo ImpTypes"
    kc imp-typing && rel ImpTypes
    scaffold soundness-ImpTypes libs_soundness ImpTypes
    runs prog imptypes && prog_imptypes
    dbuild ImpTypes
  fi
  runs lib kexpr && kc expr && lib kexpr KExpr
  runs lib exprtypes && kc expr-typing && lib exprtypes KExprTypes
  if runs demo ExprTypes; then
    phase "demo ExprTypes"
    kc expr && kc expr-typing && rel ExprTypes
    scaffold soundness-ExprTypes libs_soundness ExprTypes
    runs prog exprtypes && prog_exprtypes
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
    runs prog impplustypes && prog_impplustypes
    dbuild ImpPlusTypes
  fi
  # no stuck states (design.md §3.9): the stack machine, every case automatic; its variant without
  # `pop`'s underflow rule, whose one case is refuted by hand; with priorities (SND-15), every case
  # automatic, some by rules of different ranks on different branches
  runs lib vm && prog_lib vm KVm
  runs lib vmstuck && prog_lib vmstuck KVmStuck
  runs lib vmpri && prog_lib vmpri KVmPri
  # with `<k>` in a cell map (SND-14): coroutines, every case automatic (a resume reads the child it
  # waits on); with a join that can wait on any process, whose deadlock is refuted by hand
  runs lib coro && prog_lib coro Coro
  runs lib corojoin && prog_lib corojoin CoroJoin
  # under a kind 2 invariant: a coordination script's tasks wait on shared cells, so the rank reads the
  # script (`--rank`); `resume` is proved by hand
  runs prog handoff && prog_handoff
  phase "diff soundness"
  diffs imptypes kexpr exprtypes impplus impplustypes vm vmstuck vmpri coro corojoin
}
