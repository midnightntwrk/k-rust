# shellcheck shell=bash
# The confluence area: `confluence` (RaceConf: every schedule of the fixture race, library race;
# SimpleConf: SIMPLE's steps of two threads joined generically, library simple, with SIMPLE's
# pairs of rules classified; UtxoConf: the same for the fixture utxo, coroutines over a UTXO
# ledger, library utxo; HandoffConf: the same for the fixture handoff, tasks of a coordination
# script run when their inputs are ready, library handoff; HandoffSeqRel: the script run in its
# order, the fixture handoffseq, into handoff, library handoffseq). Registry: confluence.py.

name_confluence() {
  case $1 in
    race) echo Race ;;
    utxo) echo Utxo ;;
    handoff) echo Handoff ;;
    handoffseq) echo HandoffSeq ;;
    *) return 1 ;;
  esac
}

gen_confluence() {
  case $1 in
    # the generator's fixture whose workers interleave (tests/fixtures/race)
    race) libs_fixture_args "$1" ;;
    # coroutines in a cell map over a UTXO ledger (tests/fixtures/utxo)
    utxo) libs_fixture_args "$1" ;;
    # a coordination script's tasks over processes resumed segment by segment (tests/fixtures/handoff)
    handoff) libs_fixture_args "$1" ;;
    # the same script run in its order (tests/fixtures/handoffseq)
    handoffseq) libs_fixture_args "$1" ;;
    *) return 1 ;;
  esac
  return 0
}

# libs_confluence NS: the confluence scaffold of demo NS (RaceConf: the fixture race, by worker in
# `NS/Views.lean` and `NS/Slots.lean`, and with every pair of rules a slot in `NS/Pairs/`; SimpleConf: the views of
# SIMPLE's rules by thread, `NS/Views.lean`, with SIMPLE's pairs of rules counted) and its report
# `NS/confluence.toml` (or OUT for SimpleConf).
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
        --threads tasks --obs vals --assume-invariant HandoffConf.Wf --invariant-module HandoffConf.Inv \
        --slots "$DEMOS/HandoffConf/HandoffConf/Slots.lean" --hand-module HandoffConf.Hand \
        --open-joins "$DEMOS/HandoffConf/open-joins.txt" \
        --out "$DEMOS/HandoffConf/HandoffConf/Views.lean" --report "$DEMOS/HandoffConf/confluence.toml" ;;
    SimpleConf) "$G" confluence --kore "$(kore_dir simple)/definition.kore" --name KSimple --ns SimpleConf \
        --threads threads --obs output --out "$DEMOS/SimpleConf/SimpleConf/Views.lean" --report "$2" ;;
    *) echo "libs_confluence: unknown demo $1" >&2; return 2 ;;
  esac
}

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

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
    dbuild RaceConf
  fi
  # the views by process of the fixture utxo (`confluence --threads procs`), as SimpleConf's, and
  # the joins they leave as slots (`--slots`): generic, or proved in `UtxoConf/Hand.lean`
  if runs demo UtxoConf; then
    phase "scaffold UtxoConf"
    partlib utxo Utxo.Preserves
    scaffold confluence-UtxoConf libs_confluence UtxoConf
    dbuild UtxoConf
  fi
  # the views by task of the fixture handoff (`confluence --threads tasks`): readiness in the rules,
  # a resume's whole segment one step; under the script's well-formedness (no step of a process
  # named twice), which the hand module `HandoffConf/Inv.lean` states and `Hand.lean` uses for the
  # slots the generic attempts leave
  if runs demo HandoffConf; then
    phase "scaffold HandoffConf"
    partlib handoff Handoff.Preserves
    scaffold confluence-HandoffConf libs_confluence HandoffConf
    dbuild HandoffConf
  fi
  # the script run in its order (the fixture handoffseq) into handoff, by hand: a run of handoffseq
  # to the script's end is a run of handoff, so every terminal run of handoff ends where it does
  # (`HandoffSeqRel.result_unique`, through HandoffConf's `terminal_unique`, built just above)
  if runs demo HandoffSeqRel; then
    phase "build HandoffSeqRel"
    partlib handoffseq HandoffSeq.Rules
    dbuild HandoffSeqRel
  fi
  # SIMPLE's pairs of rules for confluence modulo scheduling, counted, with what the views by thread
  # leave open (`k2lean confluence --threads`): a recorded output; the views built against the
  # library simple (core)
  if runs output simple-confluence.toml; then
    phase "confluence SimpleConf"
    kc simple && scaffold "confluence SimpleConf" libs_confluence SimpleConf "$MEAS/simple-confluence.toml" &&
      { ! runs demo SimpleConf || dbuild SimpleConf; }
  fi
}
