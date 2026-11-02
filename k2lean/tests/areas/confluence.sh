# shellcheck shell=bash
# The confluence area: `confluence` (RaceConf: every schedule of the fixture race, library race;
# SimpleConf: SIMPLE's steps of two threads joined generically, library simple, with SIMPLE's
# pairs of rules classified and slots refuted at peaks its witness programs reach; UtxoConf: the same for the fixture utxo, coroutines over a UTXO
# ledger, library utxo; HandoffConf: the same for the fixture handoff, tasks of a coordination
# script run when their inputs are ready, library handoff; HandoffSeqRel: the script run in its
# order, the fixture handoffseq, into handoff, library handoffseq; DrfConf: workers writing one
# cell, the fixture drf, a slot refuted at a peak a program reaches, library drf; TwoConf: the
# two-layer prototype, the fixture twolayer, a coroutine language run segment by segment under a
# coordination script, library twolayer; TwoOutConf: the same under a weaker legality, a race
# refuted from a legal start, library twolayerout; HandoffRaceConf: handoff without its script's
# well-formedness, its races refuted at an instance of its parameters, library handoff; TwoParamConf:
# its parameterized form, the fixture twoparam, a segment's result a parameter of the definition,
# library twoparam; TwoParamOkConf: the same under its outputs' invariant alone, its races refuted from
# legal starts at an instance, library twoparamok; TwoParamInst: that parameter
# from the coroutine language on its own, the fixture corout, library corout; TwoParamEnds and
# TwoParamTx (B's): every segment ends, and every order of a script ends in its run's result;
# TwoLayerTx (B's): the same statement for the combined form, the fixture twolayer (its measure);
# ImpPlusConf: IMP++'s threads joined up to the flush of K's stdout stream, its races refuted at
# peaks of four programs (demos/ImpPlusConf/witnesses), library impplus; RaceLogConf: modulo an
# equivalence the author states, the fixture racelog, workers logging their steps, library racelog;
# JobsConf: the same without threads, the fixture jobs, library jobs; with priority ranks,
# RaceLogOwConf and JobsOwConf: the same modulo the equivalence over the fixtures with an `owise`
# rule, tests/racelog-owise.py and tests/jobs-owise.py, libraries racelogow and jobsow; JobsRmConf and
# JobsDropConf: jobs whose steps remove bindings of the map, tests/jobs-remove.py, libraries jobsrm
# and jobsdrop; UtxoRelConf: utxo with cells its processes write and no rule reads, by process modulo
# the equivalence, tests/utxo-relaxed.py, library utxorel). Registry: confluence.py.

kore_confluence() {
  case $1 in
    # the fixture racelog with a spawn of no work skipped by an `owise` rule (tests/racelog-owise.py,
    # priority 200 after the default 50)
    racelog-owise) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/racelog-owise.py" "$FIXTURES/racelog/racelog.k" "$2.src/racelog.k" || return 2
      f=$2.src/racelog.k m=RACELOG s=RACELOG-SYNTAX inc=$2.src ;;
    # the fixture jobs with a job that is not positive run last by an `owise` rule
    # (tests/jobs-owise.py)
    jobs-owise) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/jobs-owise.py" "$FIXTURES/jobs/jobs.k" "$2.src/jobs.k" || return 2
      f=$2.src/jobs.k m=JOBS s=JOBS-SYNTAX inc=$2.src ;;
    # the fixture jobs with each job removed when it runs, or dropped once it has run
    # (tests/jobs-remove.py)
    jobs-remove | jobs-drop) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/jobs-remove.py" "$FIXTURES/jobs/jobs.k" "$2.src/jobs.k" "${1#jobs-}" || return 2
      f=$2.src/jobs.k m=JOBS s=JOBS-SYNTAX inc=$2.src ;;
    # the fixture utxo with the last creator and a log of the outputs created and spent
    # (tests/utxo-relaxed.py)
    utxo-relaxed) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/utxo-relaxed.py" "$FIXTURES/utxo/utxo.k" "$2.src/utxo.k" || return 2
      f=$2.src/utxo.k m=UTXO s=UTXO-SYNTAX inc=$2.src ;;
    *) return 1 ;;
  esac
}

name_confluence() {
  case $1 in
    race) echo Race ;;
    utxo) echo Utxo ;;
    handoff) echo Handoff ;;
    handoffseq) echo HandoffSeq ;;
    drf) echo Drf ;;
    twolayer | twolayerout) echo TwoLayer ;;
    twoparam | twoparamok) echo TwoParam ;;
    corout) echo Corout ;;
    racelog) echo RaceLog ;;
    jobs) echo Jobs ;;
    racelogow) echo RaceLogOw ;;
    jobsow) echo JobsOw ;;
    jobsrm) echo JobsRm ;;
    jobsdrop) echo JobsDrop ;;
    utxorel) echo UtxoRel ;;
    *) return 1 ;;
  esac
}

gen_confluence() {
  case $1 in
    # the generator's fixture whose workers interleave (tests/fixtures/race)
    race) libs_fixture_args "$1" ;;
    # coroutines in a cell map over a UTXO ledger (tests/fixtures/utxo)
    utxo) libs_fixture_args "$1" ;;
    # a coordination script's tasks over processes resumed segment by segment (tests/fixtures/handoff),
    # with its script's well-formedness `wf` as a kind 1 invariant (no claim named twice)
    handoff) libs_fixture_args "$1"; GEN_ARGS+=(--invariant wf@T) ;;
    # the same script run in its order (tests/fixtures/handoffseq)
    handoffseq) libs_fixture_args "$1" ;;
    # workers writing one cell, the last write winning (tests/fixtures/drf), with its data-race
    # freedom `drfOk` as a kind 1 invariant (at most one write to <acc> pending)
    drf) libs_fixture_args "$1"; GEN_ARGS+=(--invariant drfOk@T) ;;
    # the two-layer prototype (tests/fixtures/twolayer, docs/direction.md §8 step 4): the script's
    # tasks run the segments of a coroutine language, with the script's well-formedness `wf`
    twolayer) libs_fixture_args "$1"; GEN_ARGS+=(--invariant wf@T --measure measure@T) ;;
    # the same fixture under the weaker legality `wfOut` (`wf` without the spends' claims), for
    # the demonstration TwoOutConf
    twolayerout) libs_fixture_args twolayer; GEN_ARGS+=(--invariant wfOut@T) ;;
    # its parameterized form (tests/fixtures/twoparam): a resume is one step, the segment's register
    # and code functions with no equations (`class Hooks`), with the same well-formedness `wf` and
    # the outputs' invariant `valsOk` (every output below its process's count, which tells the
    # output a resume spends from the one it writes, INV-16, CNF-33); its measure (the work left, a
    # weight per task summed over <tasks>) is lowered by every rule (`gen --measure`, INV-17)
    twoparam) libs_fixture_args "$1"; GEN_ARGS+=(--invariant wf@T --invariant valsOk@T --measure measure@T) ;;
    # the same fixture under `valsOk` alone, for the demonstration TwoParamOkConf
    twoparamok) libs_fixture_args twoparam; GEN_ARGS+=(--invariant valsOk@T) ;;
    # the coroutine language on its own (tests/fixtures/corout), deterministic; its measure (the
    # steps left, `measure` in K) is lowered by every rule (`gen --measure`, INV-15); where code is
    # on <k> (`kOk`), a configuration with no rule that applies is a segment end, a `yield` or the
    # code's end (`segEnd`; `gen --progress`, SND-19), so a segment never stops elsewhere
    corout) libs_fixture_args "$1"
      GEN_ARGS+=(--measure measure@T --invariant kOk@k --progress --ending segEnd@k) ;;
    # the fixture race with each step logged and its worker written to a cell no rule reads
    # (tests/fixtures/racelog), for `confluence --equiv`
    racelog) libs_fixture_args "$1" ;;
    # a map of jobs run in any order, each logged (tests/fixtures/jobs), for `confluence --equiv`
    # without threads
    jobs) libs_fixture_args "$1" ;;
    # the same two with an `owise` rule, two priority ranks (tests/racelog-owise.py,
    # tests/jobs-owise.py), for `confluence --equiv` with priorities
    racelogow) GEN_ARGS=(--kore "$(kore_dir racelog-owise)/definition.kore" --runtime "$(kore_dir racelog-owise)/runtime.json"
            --out "$o" --name RaceLogOw --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    jobsow) GEN_ARGS=(--kore "$(kore_dir jobs-owise)/definition.kore" --runtime "$(kore_dir jobs-owise)/runtime.json"
            --out "$o" --name JobsOw --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    # jobs whose steps remove bindings of the map (tests/jobs-remove.py), for `confluence --equiv`
    # without threads
    jobsrm) GEN_ARGS=(--kore "$(kore_dir jobs-remove)/definition.kore" --runtime "$(kore_dir jobs-remove)/runtime.json"
            --out "$o" --name JobsRm --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    jobsdrop) GEN_ARGS=(--kore "$(kore_dir jobs-drop)/definition.kore" --runtime "$(kore_dir jobs-drop)/runtime.json"
            --out "$o" --name JobsDrop --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    # utxo with cells its processes write and no rule reads (tests/utxo-relaxed.py), for
    # `confluence --threads --equiv`
    utxorel) GEN_ARGS=(--kore "$(kore_dir utxo-relaxed)/definition.kore" --runtime "$(kore_dir utxo-relaxed)/runtime.json"
            --out "$o" --name UtxoRel --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    *) return 1 ;;
  esac
  return 0
}

# libs_confluence NS: the confluence scaffold of demo NS (RaceConf: the fixture race, by worker in
# `NS/Views.lean` and `NS/Slots.lean`, and with every pair of rules a slot in `NS/Pairs/`; SimpleConf: the views of
# SIMPLE's rules by thread, `NS/Views.lean`, and its slots, `NS/Slots.lean`, with SIMPLE's pairs of
# rules counted) and its report `NS/confluence.toml` (or OUT for SimpleConf).
# HandoffSeqRel: `Tr.lean`, the script of handoffseq translated to handoff's (`--roots`; the two
# syntax modules differ in name, so the symbols pair by the fixtures' syntax definitions)
relate_confluence() {
  case $1 in
    HandoffSeqRel) na=HandoffSeq ka=$(libs_fixture handoffseq) nb=Handoff kd=$(libs_fixture handoff)
      extra=(--roots SortPgm) ;;
    *) return 1 ;;
  esac
}
# simple_witnesses DIR: SIMPLE's witness programs, each beside its initial configuration (krust's
# `krun --depth 0`): `div-nondet`, whose division's strict operands have effects, and the demo's
# (demos/SimpleConf/witnesses): strict operators with operands to evaluate, two threads declaring,
# reading and writing at once, and threads that lock, meet and throw, whose peaks refute the slots
# listed `| refuted NAME`.
# krun reads stdin, so it gets /dev/null: a gate run in the background whose stdin never closes would
# block there.
simple_witnesses() {
  rm -rf "${1:?}" && mkdir -p "$1" &&
    cp "$SD/tests/diverse/div-nondet.simple" "$DEMOS"/SimpleConf/witnesses/*.simple "$1/" &&
    for p in "$1"/*.simple; do
      "$KRUST" krun --definition "$(kore_dir simple)" --depth 0 --sort Stmt "$p" < /dev/null > "${p%.simple}.kore" || return 1
    done
}
# impplus_witnesses DIR: IMP++'s witness programs (demos/ImpPlusConf/witnesses), each beside its initial
# configuration (krust's `krun --depth 0`): two threads printing, assigning, incrementing, declaring and
# spawning at once, and strict operators with operands to evaluate, whose peaks refute the slots
# listed `| refuted NAME`.
impplus_witnesses() {
  rm -rf "${1:?}" && mkdir -p "$1" && cp "$DEMOS"/ImpPlusConf/witnesses/*.imp "$1/" &&
    for p in "$1"/*.imp; do
      "$KRUST" krun --definition "$(kore_dir impplus)" --depth 0 --sort Stmts "$p" < /dev/null > "${p%.imp}.kore" || return 1
    done
}
libs_confluence() {
  case $1 in
    RaceConf) "$G" confluence --kore "$(libs_fixture race)/definition.kore" --name Race --ns RaceConf \
        --threads workers --obs acc --slots "$DEMOS/RaceConf/RaceConf/Slots.lean" \
        --out "$DEMOS/RaceConf/RaceConf/Views.lean" --report "$DEMOS/RaceConf/confluence.toml" &&
      mkdir -p "$DEMOS/RaceConf/RaceConf/Pairs" &&
      "$G" confluence --kore "$(libs_fixture race)/definition.kore" --name Race --ns RaceConf.Pairs --obs acc \
        --views-module RaceConf.Pairs.Views --slots "$DEMOS/RaceConf/RaceConf/Pairs/Slots.lean" \
        --out "$DEMOS/RaceConf/RaceConf/Pairs/Views.lean" --report "$DEMOS/RaceConf/pairs.toml" ;;
    UtxoConf) "$G" confluence --kore "$(libs_fixture utxo)/definition.kore" --name Utxo --ns UtxoConf \
        --threads procs --obs ledger --slots "$DEMOS/UtxoConf/UtxoConf/Slots.lean" --hand-module UtxoConf.Hand \
        --open-joins "$DEMOS/UtxoConf/open-joins.txt" \
        --out "$DEMOS/UtxoConf/UtxoConf/Views.lean" --report "$DEMOS/UtxoConf/confluence.toml" ;;
    HandoffConf) "$G" confluence --kore "$(libs_fixture handoff)/definition.kore" --name Handoff --ns HandoffConf \
        --threads tasks --obs vals --assume-invariant Handoff.Invariant \
        --slots "$DEMOS/HandoffConf/HandoffConf/Slots.lean" \
        --out "$DEMOS/HandoffConf/HandoffConf/Views.lean" --report "$DEMOS/HandoffConf/confluence.toml" ;;
    DrfConf) "$G" confluence --kore "$(libs_fixture drf)/definition.kore" --name Drf --ns DrfConf \
        --threads workers --obs acc --slots "$DEMOS/DrfConf/DrfConf/Slots.lean" \
        --open-joins "$DEMOS/DrfConf/open-joins.txt" --witnesses "$(libs_fixture drf)/witnesses" \
        --out "$DEMOS/DrfConf/DrfConf/Views.lean" --report "$DEMOS/DrfConf/confluence.toml" &&
      mkdir -p "$DEMOS/DrfConf/DrfConf/Legal" &&
      "$G" confluence --kore "$(libs_fixture drf)/definition.kore" --name Drf --ns DrfConf.Legal \
        --threads workers --obs acc --assume-invariant Drf.Invariant --views-module DrfConf.Legal.Views \
        --slots "$DEMOS/DrfConf/DrfConf/Legal/Slots.lean" \
        --out "$DEMOS/DrfConf/DrfConf/Legal/Views.lean" --report "$DEMOS/DrfConf/legal.toml" ;;
    # the two-layer prototype: the races of two tasks refuted together by two runs of each witness
    # (`Open.refuted`), and each at a peak a witness reaches (`| refuted NAME`); every slot generic
    # under the script's well-formedness `wf` (`TwoConf.Legal`)
    TwoConf) "$G" confluence --kore "$(libs_fixture twolayer)/definition.kore" --name TwoLayer --ns TwoConf \
        --threads tasks --obs vals --slots "$DEMOS/TwoConf/TwoConf/Slots.lean" \
        --open-joins "$DEMOS/TwoConf/open-joins.txt" --witnesses "$(libs_fixture twolayer)/witnesses" \
        --out "$DEMOS/TwoConf/TwoConf/Views.lean" --report "$DEMOS/TwoConf/confluence.toml" &&
      mkdir -p "$DEMOS/TwoConf/TwoConf/Legal" &&
      "$G" confluence --kore "$(libs_fixture twolayer)/definition.kore" --name TwoLayer --ns TwoConf.Legal \
        --threads tasks --obs vals --assume-invariant TwoLayer.Invariant --views-module TwoConf.Legal.Views \
        --slots "$DEMOS/TwoConf/TwoConf/Legal/Slots.lean" \
        --out "$DEMOS/TwoConf/TwoConf/Legal/Views.lean" --report "$DEMOS/TwoConf/legal.toml" ;;
    # under the weaker `wfOut` the race of two spends remains: refuted by two runs of a program
    # `wfOut` admits (`witness.«two-spends».legal`, the hand module's) and at a peak it reaches
    TwoOutConf) rm -rf "${W:?}/two-out-witnesses" && mkdir -p "$W/two-out-witnesses" &&
      cp "$(libs_fixture twolayer)"/witnesses/two-spends.* "$W/two-out-witnesses/" &&
      "$G" confluence --kore "$(libs_fixture twolayer)/definition.kore" --name TwoLayer --ns TwoOutConf \
        --threads tasks --obs vals --assume-invariant TwoLayer.Invariant --hand-module TwoOutConf.Hand \
        --open-joins "$DEMOS/TwoOutConf/open-joins.txt" --witnesses "$W/two-out-witnesses" \
        --slots "$DEMOS/TwoOutConf/TwoOutConf/Slots.lean" \
        --out "$DEMOS/TwoOutConf/TwoOutConf/Views.lean" --report "$DEMOS/TwoOutConf/confluence.toml" ;;
    # without the script's well-formedness the races of two creations and two resumes remain:
    # each refuted at a peak of a program that has it, run at the instance `HandoffRaceConf.sum`
    HandoffRaceConf) "$G" confluence --kore "$(libs_fixture handoff)/definition.kore" --name Handoff \
        --ns HandoffRaceConf --threads tasks --obs vals --open-joins "$DEMOS/HandoffRaceConf/open-joins.txt" \
        --witnesses "$(libs_fixture handoff)/witnesses" \
        --witness-instance HandoffRaceConf.sum --witness-instance-module HandoffRaceConf.Inst \
        --slots "$DEMOS/HandoffRaceConf/HandoffRaceConf/Slots.lean" \
        --out "$DEMOS/HandoffRaceConf/HandoffRaceConf/Views.lean" --report "$DEMOS/HandoffRaceConf/confluence.toml" ;;
    # the parameterized form: every slot generic under `wf`, for every instance of the parameters
    TwoParamConf) "$G" confluence --kore "$(libs_fixture twoparam)/definition.kore" --name TwoParam --ns TwoParamConf \
        --threads tasks --obs vals --assume-invariant TwoParam.Invariant \
        --slots "$DEMOS/TwoParamConf/TwoParamConf/Slots.lean" \
        --out "$DEMOS/TwoParamConf/TwoParamConf/Views.lean" --report "$DEMOS/TwoParamConf/confluence.toml" ;;
    # under `valsOk` alone the same races remain: refuted from programs `valsOk` admits
    # (`witness.W.legal`, generated: each is an initial configuration, `Invariant.init_holds`) at the
    # instance `TwoParamOkConf.seg` (TwoParamOkConf/Hand.lean)
    TwoParamOkConf) "$G" confluence --kore "$(libs_fixture twoparam)/definition.kore" --name TwoParam \
        --ns TwoParamOkConf --threads tasks --obs vals --assume-invariant TwoParam.Invariant \
        --open-joins "$DEMOS/TwoParamOkConf/open-joins.txt" \
        --witnesses "$(libs_fixture twoparam)/witnesses" --witness-instance TwoParamOkConf.seg \
        --witness-instance-module TwoParamOkConf.Hand \
        --slots "$DEMOS/TwoParamOkConf/TwoParamOkConf/Slots.lean" \
        --out "$DEMOS/TwoParamOkConf/TwoParamOkConf/Views.lean" --report "$DEMOS/TwoParamOkConf/confluence.toml" ;;
    # the translations of code between twoparam and corout, both ways (`relate --roots SortStmts`, by
    # the fixtures' syntax definitions), for the instance `TwoParamInst/Inst.lean`
    TwoParamInst) local a b
      a=$(libs_fixture twoparam) b=$(libs_fixture corout)
      "$G" relate --kore-a "$a/definition.kore" --syntax-a "$a/syntaxDefinition.kore" --name-a TwoParam \
        --kore-b "$b/definition.kore" --syntax-b "$b/syntaxDefinition.kore" --name-b Corout \
        --ns TwoParamInst.Tr --roots SortStmts \
        --out "$DEMOS/TwoParamInst/TwoParamInst/Tr.lean" --report "$DEMOS/TwoParamInst/tr.toml" &&
      "$G" relate --kore-a "$b/definition.kore" --syntax-a "$b/syntaxDefinition.kore" --name-a Corout \
        --kore-b "$a/definition.kore" --syntax-b "$a/syntaxDefinition.kore" --name-b TwoParam \
        --ns TwoParamInst.Back --roots SortStmts \
        --out "$DEMOS/TwoParamInst/TwoParamInst/Back.lean" --report "$DEMOS/TwoParamInst/back.toml" ;;
    SimpleConf) simple_witnesses "$W/simple-witnesses" &&
      "$G" confluence --kore "$(kore_dir simple)/definition.kore" --name KSimple --ns SimpleConf \
        --threads threads --obs output --slots "$DEMOS/SimpleConf/SimpleConf/Slots.lean" \
        --open-joins "$DEMOS/SimpleConf/open-joins.txt" --witnesses "$W/simple-witnesses" --witness-fuel 64 \
        --out "$DEMOS/SimpleConf/SimpleConf/Views.lean" --report "$2" ;;
    ImpPlusConf) impplus_witnesses "$W/impplus-witnesses" &&
      "$G" confluence --kore "$(kore_dir impplus)/definition.kore" --name KImpPlus --ns ImpPlusConf \
        --threads threads --obs output --slots "$DEMOS/ImpPlusConf/ImpPlusConf/Slots.lean" \
        --open-joins "$DEMOS/ImpPlusConf/open-joins.txt" --witnesses "$W/impplus-witnesses" \
        --out "$DEMOS/ImpPlusConf/ImpPlusConf/Views.lean" --report "$DEMOS/ImpPlusConf/confluence.toml" ;;
    # by equality the slot of two workers' steps refuted at a peak of a program; modulo the order of
    # the log and the last writer (`--equiv`, `RaceLogConf.Equiv`) every slot generic
    RaceLogConf) "$G" confluence --kore "$(libs_fixture racelog)/definition.kore" --name RaceLog --ns RaceLogConf \
        --threads workers --open-joins "$DEMOS/RaceLogConf/open-joins.txt" --witnesses "$(libs_fixture racelog)/witnesses" \
        --slots "$DEMOS/RaceLogConf/RaceLogConf/Slots.lean" \
        --out "$DEMOS/RaceLogConf/RaceLogConf/Views.lean" --report "$DEMOS/RaceLogConf/confluence.toml" &&
      mkdir -p "$DEMOS/RaceLogConf/RaceLogConf/Equiv" &&
      "$G" confluence --kore "$(libs_fixture racelog)/definition.kore" --name RaceLog --ns RaceLogConf.Equiv \
        --threads workers --obs acc --equiv log=perm,last=any --views-module RaceLogConf.Equiv.Views \
        --slots "$DEMOS/RaceLogConf/RaceLogConf/Equiv/Slots.lean" \
        --out "$DEMOS/RaceLogConf/RaceLogConf/Equiv/Views.lean" --report "$DEMOS/RaceLogConf/equiv.toml" ;;
    # the same without threads (every ordered pair of rules a slot): by equality the slot open, refuted
    # with the others by two runs of a program (`Open.refuted`); modulo the order of `<done>` generic
    JobsConf) "$G" confluence --kore "$(libs_fixture jobs)/definition.kore" --name Jobs --ns JobsConf \
        --open-joins "$DEMOS/JobsConf/open-joins.txt" --witnesses "$(libs_fixture jobs)/witnesses" \
        --slots "$DEMOS/JobsConf/JobsConf/Slots.lean" \
        --out "$DEMOS/JobsConf/JobsConf/Views.lean" --report "$DEMOS/JobsConf/confluence.toml" &&
      mkdir -p "$DEMOS/JobsConf/JobsConf/Equiv" &&
      "$G" confluence --kore "$(libs_fixture jobs)/definition.kore" --name Jobs --ns JobsConf.Equiv \
        --obs total --equiv done=perm --views-module JobsConf.Equiv.Views \
        --slots "$DEMOS/JobsConf/JobsConf/Equiv/Slots.lean" \
        --out "$DEMOS/JobsConf/JobsConf/Equiv/Views.lean" --report "$DEMOS/JobsConf/equiv.toml" ;;
    # the same two with an `owise` rule, modulo the same equivalences: a step of the later rank owes
    # at the related configuration, and after another step, that no rule of the earlier applies
    RaceLogOwConf) "$G" confluence --kore "$(kore_dir racelog-owise)/definition.kore" --name RaceLogOw --ns RaceLogOwConf \
        --threads workers --obs acc --equiv log=perm,last=any --views-module RaceLogOwConf.Views \
        --slots "$DEMOS/RaceLogOwConf/RaceLogOwConf/Slots.lean" \
        --out "$DEMOS/RaceLogOwConf/RaceLogOwConf/Views.lean" --report "$DEMOS/RaceLogOwConf/confluence.toml" ;;
    JobsOwConf) "$G" confluence --kore "$(kore_dir jobs-owise)/definition.kore" --name JobsOw --ns JobsOwConf \
        --obs total --equiv done=perm --views-module JobsOwConf.Views \
        --slots "$DEMOS/JobsOwConf/JobsOwConf/Slots.lean" \
        --out "$DEMOS/JobsOwConf/JobsOwConf/Views.lean" --report "$DEMOS/JobsOwConf/confluence.toml" ;;
    # jobs whose steps remove bindings of the map, modulo the same equivalence: two removals, or a
    # removal and an update, at two bindings commute
    JobsRmConf) "$G" confluence --kore "$(kore_dir jobs-remove)/definition.kore" --name JobsRm --ns JobsRmConf \
        --obs total --equiv done=perm --views-module JobsRmConf.Views \
        --slots "$DEMOS/JobsRmConf/JobsRmConf/Slots.lean" \
        --out "$DEMOS/JobsRmConf/JobsRmConf/Views.lean" --report "$DEMOS/JobsRmConf/confluence.toml" ;;
    JobsDropConf) "$G" confluence --kore "$(kore_dir jobs-drop)/definition.kore" --name JobsDrop --ns JobsDropConf \
        --obs total --equiv done=perm --views-module JobsDropConf.Views \
        --slots "$DEMOS/JobsDropConf/JobsDropConf/Slots.lean" \
        --out "$DEMOS/JobsDropConf/JobsDropConf/Views.lean" --report "$DEMOS/JobsDropConf/confluence.toml" ;;
    # utxo with the last creator and a log, by process modulo `last` not compared and `log` up to
    # order: two creations or spends at two keys of the ledger commute (relaxed cells in the views'
    # classes)
    UtxoRelConf) "$G" confluence --kore "$(kore_dir utxo-relaxed)/definition.kore" --name UtxoRel --ns UtxoRelConf \
        --threads procs --obs ledger --equiv last=any,log=perm --views-module UtxoRelConf.Views \
        --slots "$DEMOS/UtxoRelConf/UtxoRelConf/Slots.lean" --hand-module UtxoRelConf.Hand \
        --open-joins "$DEMOS/UtxoRelConf/open-joins.txt" \
        --out "$DEMOS/UtxoRelConf/UtxoRelConf/Views.lean" --report "$DEMOS/UtxoRelConf/confluence.toml" ;;
    *) echo "libs_confluence: unknown demo $1" >&2; return 2 ;;
  esac
}

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

# dbuild_slots PROJECT: build confluence demo PROJECT, then read its frozen names' statuses from the
# built environment (`k2l-eval --result`), by which gate-check compares its slots by name
dbuild_slots() {
  if lbuild "$D/$1" "build-$1"; then
    ok "build $1" "$L/build-$1.log"
    if (cd "$D/$1" && "$RT" lake env "$EV" --result "$1" "$L/result-demo-$1.json" "$1") > "$L/result-demo-$1.log" 2>&1
    then ok "result demo $1" "$L/result-demo-$1.log"; else bad "result demo $1" "$L/result-demo-$1.log"; fi
  else bad "build $1" "$L/build-$1.log"; fi
}

needs_confluence() {
  if runs output simple-confluence.toml; then
    [ -d "$SD" ] || need "SIMPLE's sources at $SD (set GATE_K_CHECKOUT)"
  fi
  return 0
}

gate_confluence() {
  # confluence modulo scheduling (docs/design.md, section 3.6) of the fixture race, by worker and
  # with every pair of rules a slot, its library built only as far as the demo needs
  if runs demo RaceConf; then
    phase "scaffold RaceConf"
    partlib race Race.Preserves
    scaffold confluence-RaceConf libs_confluence RaceConf
    dbuild_slots RaceConf
  fi
  # the views by process of the fixture utxo (`confluence --threads procs`), as SimpleConf's, and
  # the joins they leave as slots (`--slots`): generic, or proved in `UtxoConf/Hand.lean`
  if runs demo UtxoConf; then
    phase "scaffold UtxoConf"
    partlib utxo Utxo.Preserves
    scaffold confluence-UtxoConf libs_confluence UtxoConf
    dbuild_slots UtxoConf
  fi
  # the views by task of the fixture handoff (`confluence --threads tasks`): readiness in the rules,
  # a resume's whole segment one step; under the script's well-formedness `wf` (no step of a process
  # named twice), a K function of the fixture whose preservation `gen --invariant` proves
  # (`Handoff.Invariant`), every slot generic: two tasks claiming one step are one task
  # (`k2l_one_binding`); `HandoffConf/Claims.lean` reads it order-free for `Live.lean`
  if runs demo HandoffConf; then
    phase "scaffold HandoffConf"
    partlib handoff Handoff.Invariants
    scaffold confluence-HandoffConf libs_confluence HandoffConf
    dbuild_slots HandoffConf
  fi
  # the same without the script's well-formedness: two tasks may create one process or take one
  # segment of it, and each such race is refuted at a peak of a program that has it, the runs at the
  # instance `HandoffRaceConf.sum` (a running sum, `HandoffRaceConf/Inst.lean`); every other slot
  # generic for every instance. The library is HandoffConf's when its phase runs
  if runs demo HandoffRaceConf; then
    phase "scaffold HandoffRaceConf"
    runs demo HandoffConf || partlib handoff Handoff.Adequacy
    scaffold confluence-HandoffRaceConf libs_confluence HandoffRaceConf
    dbuild_slots HandoffRaceConf
  fi
  # the script run in its order (the fixture handoffseq) into handoff, the script's translation
  # generated (`relate --roots SortPgm`), the simulation by hand: a run
  # of handoffseq to the script's end is a run of handoff, so every terminal run of handoff ends where
  # it does (`HandoffSeqRel.result_unique` by `KPrelude.Forward.result_unique_of`, through
  # HandoffConf's `terminal_unique`, built just above); with HandoffConf's `terminates` (the work left
  # drops at every step), every order ends there (`HandoffSeqRel.transaction`, through `KPrelude.Ends`)
  if runs demo HandoffSeqRel; then
    phase "build HandoffSeqRel"
    partlib handoffseq HandoffSeq.Rules
    rel HandoffSeqRel
    dbuild HandoffSeqRel
  fi
  # the views by worker of the fixture drf, whose workers each write one cell: two runs of the
  # program `spawn(1); spawn(2); done` end with `<acc>` 2 and 1 (`witness.«two-workers».refutes`,
  # tests/fixtures/drf/witnesses), which refutes the slot of two writes, the only one not proved;
  # under its data-race freedom `drfOk`, a K function of the fixture whose preservation
  # `gen --invariant` proves (`Drf.Invariant`), every slot generic (`DrfConf.Legal`: two pending
  # writes claim the accumulator, so they are one worker's, `k2l_one_binding`)
  if runs demo DrfConf; then
    phase "scaffold DrfConf"
    partlib drf Drf.Adequacy
    scaffold confluence-DrfConf libs_confluence DrfConf
    dbuild_slots DrfConf
  fi
  # the two-layer prototype (docs/direction.md §8 step 4): the views by task of the fixture twolayer,
  # a resume running the process's segment in the resuming task; the races of two tasks for one
  # creation, resume or spend refuted together by two runs of each witness; under the script's
  # well-formedness `wf` (`TwoLayer.Invariant`, preserved by every rule) every slot generic
  if runs demo TwoConf; then
    phase "scaffold TwoConf"
    partlib twolayer TwoLayer
    scaffold confluence-TwoConf libs_confluence TwoConf
    dbuild_slots TwoConf
  fi
  # the same under the weaker legality `wfOut` (library twolayerout, started from twolayer's build:
  # they differ in the invariant's modules only): the slot of two resumes spending one output open,
  # refuted from a program `wfOut` admits, by two runs and at a peak; every other slot generic
  if runs demo TwoOutConf; then
    phase "scaffold TwoOutConf"
    seed_lake twolayerout twolayer
    partlib twolayerout TwoLayer
    scaffold confluence-TwoOutConf libs_confluence TwoOutConf
    dbuild_slots TwoOutConf
  fi
  # its parameterized form: the fixture twoparam, a resume's whole segment one step whose register
  # and code are parameters (`TwoParam.Hooks`); under `wf` every slot generic for every instance,
  # a resume that spends an output and writes its own changing <vals> at two keys (`MCh.fx_move`)
  if runs demo TwoParamConf; then
    phase "scaffold TwoParamConf"
    partlib twoparam TwoParam
    scaffold confluence-TwoParamConf libs_confluence TwoParamConf
    dbuild_slots TwoParamConf
  fi
  # the same under the outputs' invariant `valsOk` alone (library twoparamok, started from twoparam's
  # build): the races of two creations, resumes and spends remain, each refuted at a peak of a
  # program `valsOk` admits (an initial configuration), the runs at the instance `TwoParamOkConf.seg`
  # (a bounded run of the coroutine language's code, the hand module's); every other slot generic
  if runs demo TwoParamOkConf; then
    phase "scaffold TwoParamOkConf"
    seed_lake twoparamok twoparam
    partlib twoparamok TwoParam
    scaffold confluence-TwoParamOkConf libs_confluence TwoParamOkConf
    dbuild_slots TwoParamOkConf
  fi
  # the parameters from the coroutine language on its own (the fixture corout, deterministic): a
  # segment is corout's run to the first configuration that does not step, unique
  # (`Paths.FirstReach.unique`), by hand in `TwoParamInst/Inst.lean` over the translations of code
  # `relate` generates; TwoParamConf's `terminal_unique` at that instance; built against
  # TwoParamConf's phase
  if runs demo TwoParamInst; then
    phase "scaffold TwoParamInst"
    partlib corout Corout
    scaffold relate-TwoParamInst libs_confluence TwoParamInst
    dbuild TwoParamInst
  fi
  # every segment ends (B's): corout's measure, lowered by every rule (`Corout.Measure`), so the
  # hooks of TwoParamInst always have a value (`TwoParamEnds.hooks_some`); built against
  # TwoParamInst's phase
  if runs demo TwoParamEnds; then
    phase "build TwoParamEnds"
    dbuild TwoParamEnds
  fi
  # the transaction statement of the parameterized form (B's): a well-formed script with one run to
  # no task left ends in that run's configuration in every order (twoparam's measure, generated in
  # generated/twoparam, with TwoParamConf's `terminal_unique`); built against TwoParamConf's phase
  if runs demo TwoParamTx; then
    phase "build TwoParamTx"
    dbuild TwoParamTx
  fi
  # the same for the combined form (B's): the work left in the tasks and in the suspended processes'
  # code (twolayer's measure, generated in generated/twolayer), with TwoConf's legal
  # `terminal_unique`; built against TwoConf's phase
  if runs demo TwoLayerTx; then
    phase "build TwoLayerTx"
    dbuild TwoLayerTx
  fi
  # IMP++ (the soundness area's library impplus): threads, `print`, K's stdout stream at priorities 25
  # and 30 before the language's rules, and the store a map changed at some bindings; up to the
  # flush of the stream (docs/design.md, section 3.6, "Priorities and the flush") `print` and a step
  # of another thread join generically, and the theorem is the observation's (`obs_unique`)
  if runs demo ImpPlusConf; then
    phase "scaffold ImpPlusConf"
    kc impplus && partlib impplus KImpPlus.Preserves &&
      scaffold confluence-ImpPlusConf libs_confluence ImpPlusConf && dbuild_slots ImpPlusConf
  fi
  # confluence modulo an equivalence the author states (`confluence --equiv`, docs/design.md,
  # section 3.6): the fixture racelog, whose workers log their steps, by worker; by equality the slot
  # of two workers' steps is refuted at a peak of the program `two`, and modulo the order of `<log>`
  # and the last writer `<last>` every slot is generic, each rule keeping the equivalence
  # (`equiv.sim.r`)
  if runs demo RaceLogConf; then
    phase "scaffold RaceLogConf"
    partlib racelog RaceLog.Adequacy
    scaffold confluence-RaceLogConf libs_confluence RaceLogConf
    dbuild_slots RaceLogConf
  fi
  # the same without threads: the fixture jobs, a map of jobs run in any order, each logged
  if runs demo JobsConf; then
    phase "scaffold JobsConf"
    partlib jobs Jobs.Adequacy
    scaffold confluence-JobsConf libs_confluence JobsConf
    dbuild_slots JobsConf
  fi
  # with priority ranks: the same two over the fixtures with an `owise` rule, every slot and every
  # rule's lemma generic, the priority premises at the related configuration (`k2l_pri_other`) and
  # after the other step (`k2l_pri_back`); a pair of two ranks refuted by the later's premise
  if runs demo RaceLogOwConf; then
    phase "scaffold RaceLogOwConf"
    kc racelog-owise && partlib racelogow RaceLogOw.Adequacy &&
      scaffold confluence-RaceLogOwConf libs_confluence RaceLogOwConf && dbuild_slots RaceLogOwConf
  fi
  if runs demo JobsOwConf; then
    phase "scaffold JobsOwConf"
    kc jobs-owise && partlib jobsow JobsOw.Adequacy &&
      scaffold confluence-JobsOwConf libs_confluence JobsOwConf && dbuild_slots JobsOwConf
  fi
  # removals: jobs whose steps remove bindings of the map, every slot generic, two removals and a
  # removal beside an update at two bindings commuting (`concat_element_same_or_comm_remove`,
  # `concat_element_same_or_comm_remove_update`)
  if runs demo JobsRmConf; then
    phase "scaffold JobsRmConf"
    kc jobs-remove && partlib jobsrm JobsRm.Adequacy &&
      scaffold confluence-JobsRmConf libs_confluence JobsRmConf && dbuild_slots JobsRmConf
  fi
  if runs demo JobsDropConf; then
    phase "scaffold JobsDropConf"
    kc jobs-drop && partlib jobsdrop JobsDrop.Adequacy &&
      scaffold confluence-JobsDropConf libs_confluence JobsDropConf && dbuild_slots JobsDropConf
  fi
  # relaxed cells in the views' classes: utxo whose creations and spends also write cells no rule
  # reads, joined generically at two keys of the ledger modulo the equivalence
  if runs demo UtxoRelConf; then
    phase "scaffold UtxoRelConf"
    kc utxo-relaxed && partlib utxorel UtxoRel.Preserves &&
      scaffold confluence-UtxoRelConf libs_confluence UtxoRelConf && dbuild_slots UtxoRelConf
  fi
  # SIMPLE's pairs of rules for confluence modulo scheduling, counted, with the slots the views by
  # thread leave, by premise and class (`k2lean confluence --threads --slots`): a recorded output;
  # the views and slots built against the library simple (core), the open slots false together
  # (`Open.refuted`): two runs of each witness program print different results; the slots listed
  # `| refuted W` false one by one, at peaks the program W reaches (`witness.W.peaks`)
  if runs output simple-confluence.toml; then
    phase "confluence SimpleConf"
    kc simple && scaffold "confluence SimpleConf" libs_confluence SimpleConf "$MEAS/simple-confluence.toml" &&
      { ! runs demo SimpleConf || dbuild_slots SimpleConf; }
  fi
}
