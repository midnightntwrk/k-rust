# shellcheck shell=bash
# The confluence area: `confluence` (RaceConf: every schedule of the fixture race, library race;
# SimpleConf: SIMPLE's steps of two threads joined generically, library simple, with SIMPLE's
# pairs of rules classified; UtxoConf: the same for the fixture utxo, coroutines over a UTXO
# ledger, library utxo; HandoffConf: the same for the fixture handoff, tasks of a coordination
# script run when their inputs are ready, library handoff; HandoffSeqRel: the script run in its
# order, the fixture handoffseq, into handoff, library handoffseq; DrfConf: workers writing one
# cell, the fixture drf, a slot refuted by two runs of a program, library drf; TwoConf: the
# two-layer prototype, the fixture twolayer, a coroutine language run segment by segment under a
# coordination script, library twolayer; TwoParamConf: its parameterized form, the fixture twoparam,
# a segment's result a parameter of the definition, library twoparam; TwoParamInst: that parameter
# from the coroutine language on its own, the fixture corout, library corout). Registry:
# confluence.py.

name_confluence() {
  case $1 in
    race) echo Race ;;
    utxo) echo Utxo ;;
    handoff) echo Handoff ;;
    handoffseq) echo HandoffSeq ;;
    drf) echo Drf ;;
    twolayer) echo TwoLayer ;;
    twoparam) echo TwoParam ;;
    corout) echo Corout ;;
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
    twolayer) libs_fixture_args "$1"; GEN_ARGS+=(--invariant wf@T) ;;
    # its parameterized form (tests/fixtures/twoparam): a resume is one step, the segment's register
    # and code functions with no equations (`class Hooks`), with the same well-formedness `wf`
    twoparam) libs_fixture_args "$1"; GEN_ARGS+=(--invariant wf@T) ;;
    # the coroutine language on its own (tests/fixtures/corout), deterministic
    corout) libs_fixture_args "$1" ;;
    *) return 1 ;;
  esac
  return 0
}

# libs_confluence NS: the confluence scaffold of demo NS (RaceConf: the fixture race, by worker in
# `NS/Views.lean` and `NS/Slots.lean`, and with every pair of rules a slot in `NS/Pairs/`; SimpleConf: the views of
# SIMPLE's rules by thread, `NS/Views.lean`, and its slots, `NS/Slots.lean`, with SIMPLE's pairs of
# rules counted) and its report `NS/confluence.toml` (or OUT for SimpleConf).
# simple_witnesses DIR: SIMPLE's witness programs, each beside its initial configuration (krust's
# `krun --depth 0`): `div-nondet`, whose division's strict operands have effects.
simple_witnesses() {
  rm -rf "${1:?}" && mkdir -p "$1" && cp "$SD/tests/diverse/div-nondet.simple" "$1/" &&
    "$KRUST" krun --definition "$(kore_dir simple)" --depth 0 --sort Stmt "$1/div-nondet.simple" > "$1/div-nondet.kore"
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
    # (`Open.refuted`), and every slot generic under the script's well-formedness `wf` (`TwoConf.Legal`)
    TwoConf) "$G" confluence --kore "$(libs_fixture twolayer)/definition.kore" --name TwoLayer --ns TwoConf \
        --threads tasks --obs vals --slots "$DEMOS/TwoConf/TwoConf/Slots.lean" \
        --open-joins "$DEMOS/TwoConf/open-joins.txt" --witnesses "$(libs_fixture twolayer)/witnesses" \
        --out "$DEMOS/TwoConf/TwoConf/Views.lean" --report "$DEMOS/TwoConf/confluence.toml" &&
      mkdir -p "$DEMOS/TwoConf/TwoConf/Legal" &&
      "$G" confluence --kore "$(libs_fixture twolayer)/definition.kore" --name TwoLayer --ns TwoConf.Legal \
        --threads tasks --obs vals --assume-invariant TwoLayer.Invariant --views-module TwoConf.Legal.Views \
        --slots "$DEMOS/TwoConf/TwoConf/Legal/Slots.lean" \
        --out "$DEMOS/TwoConf/TwoConf/Legal/Views.lean" --report "$DEMOS/TwoConf/legal.toml" ;;
    # the parameterized form: every slot generic under `wf`, for every instance of the parameters
    TwoParamConf) "$G" confluence --kore "$(libs_fixture twoparam)/definition.kore" --name TwoParam --ns TwoParamConf \
        --threads tasks --obs vals --assume-invariant TwoParam.Invariant \
        --slots "$DEMOS/TwoParamConf/TwoParamConf/Slots.lean" \
        --out "$DEMOS/TwoParamConf/TwoParamConf/Views.lean" --report "$DEMOS/TwoParamConf/confluence.toml" ;;
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
  # the script run in its order (the fixture handoffseq) into handoff, the simulation by hand: a run
  # of handoffseq to the script's end is a run of handoff, so every terminal run of handoff ends where
  # it does (`HandoffSeqRel.result_unique` by `KPrelude.Forward.result_unique_of`, through
  # HandoffConf's `terminal_unique`, built just above); with HandoffConf's `terminates` (the work left
  # drops at every step), every order ends there (`HandoffSeqRel.transaction`, through `KPrelude.Ends`)
  if runs demo HandoffSeqRel; then
    phase "build HandoffSeqRel"
    partlib handoffseq HandoffSeq.Rules
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
  # its parameterized form: the fixture twoparam, a resume's whole segment one step whose register
  # and code are parameters (`TwoParam.Hooks`); under `wf` every slot generic for every instance,
  # a resume that spends an output and writes its own changing <vals> at two keys (`MCh.fx_move`)
  if runs demo TwoParamConf; then
    phase "scaffold TwoParamConf"
    partlib twoparam TwoParam
    scaffold confluence-TwoParamConf libs_confluence TwoParamConf
    dbuild_slots TwoParamConf
  fi
  # the parameters from the coroutine language on its own (the fixture corout, deterministic): a
  # segment is corout's run to the first configuration that does not step, unique
  # (`Paths.FirstReach.unique`), by hand in `TwoParamInst/Inst.lean` over the translations of code
  # `relate` generates; TwoParamConf's `terminal_unique` at that instance; built against
  # TwoParamConf's phase
  if runs demo TwoParamInst; then
    phase "scaffold TwoParamInst"
    partlib corout Corout.Determinism
    scaffold relate-TwoParamInst libs_confluence TwoParamInst
    dbuild TwoParamInst
  fi
  # SIMPLE's pairs of rules for confluence modulo scheduling, counted, with the slots the views by
  # thread leave, by premise and class (`k2lean confluence --threads --slots`): a recorded output;
  # the views and slots built against the library simple (core), the open slots false together
  # (`Open.refuted`): two runs of SIMPLE's test `div-nondet` print different results
  if runs output simple-confluence.toml; then
    phase "confluence SimpleConf"
    kc simple && scaffold "confluence SimpleConf" libs_confluence SimpleConf "$MEAS/simple-confluence.toml" &&
      { ! runs demo SimpleConf || dbuild_slots SimpleConf; }
  fi
}
