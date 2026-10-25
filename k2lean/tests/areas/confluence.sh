# shellcheck shell=bash
# The confluence area: `confluence` (RaceConf: every schedule of the fixture race, library race;
# SIMPLE's pairs of rules classified, report only). Registry: confluence.py.

name_confluence() {
  case $1 in
    race) echo Race ;;
    *) return 1 ;;
  esac
}

gen_confluence() {
  case $1 in
    # the generator's fixture whose workers interleave (tests/fixtures/race)
    race) libs_fixture_args "$1" ;;
    *) return 1 ;;
  esac
  return 0
}

# libs_confluence NS: the confluence scaffold of demo NS (RaceConf: the fixture race, every pair
# generated, `NS/Confluence.lean` after the hand module `NS/Hand.lean`; SimpleConf: SIMPLE's pairs
# of rules counted, the report only) and its report `NS/confluence.toml` (or OUT for SimpleConf).
libs_confluence() {
  case $1 in
    RaceConf) "$G" confluence --kore "$(libs_fixture race)/definition.kore" --name Race --ns RaceConf --obs acc \
        --out "$DEMOS/RaceConf/RaceConf/Confluence.lean" --report "$DEMOS/RaceConf/confluence.toml" ;;
    SimpleConf) "$G" confluence --kore "$(kore_dir simple)/definition.kore" --name KSimple --report-only true \
        --report "$2" ;;
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
  # confluence modulo scheduling (docs/design.md, section 3.6) of the fixture race, its library
  # built only as far as the demo needs
  if runs demo RaceConf; then
    phase "scaffold RaceConf"
    partlib race Race.Preserves
    scaffold confluence-RaceConf libs_confluence RaceConf
    dbuild RaceConf
  fi
  # SIMPLE's pairs of rules for confluence modulo scheduling, counted (`k2lean confluence
  # --report-only`): a recorded output
  if runs output simple-confluence.toml; then
    phase "confluence SimpleConf"
    kc simple && scaffold "confluence SimpleConf" libs_confluence SimpleConf "$MEAS/simple-confluence.toml"
  fi
}
