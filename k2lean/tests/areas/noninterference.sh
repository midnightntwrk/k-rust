# shellcheck shell=bash
# The noninterference area: `noninterference` (ImpNI: kimp with the security checker
# demos/k/imp-sec.k, library impsec, over kimpni, kimp with what a store is, demos/k/imp-ni.k;
# ContractNI: the fixture contract, a contract with private state, with its checker, the fixture
# contractsec). Registry: noninterference.py.

kore_noninterference() {
  case $1 in
    imp-sec) f=$DEMOS/k/imp-sec.k m=IMP-SEC s=IMP-SEC-SYNTAX inc=$KIMP ;;
    imp-ni) f=$DEMOS/k/imp-ni.k m=IMP-NI s=IMP-SYNTAX inc=$KIMP ;;
    *) return 1 ;;
  esac
}

name_noninterference() {
  case $1 in
    impsec) echo KImpSec ;;
    kimpni) echo KImpNI ;;
    contract) echo Contract ;;
    contractsec) echo ContractSec ;;
    *) return 1 ;;
  esac
}

gen_noninterference() {
  case $1 in
    impsec) GEN_ARGS=(--kore "$(kore_dir imp-sec)/definition.kore" --runtime "$(kore_dir imp-sec)/runtime.json"
            --out "$o" --name KImpSec --prelude ../../lean
            --open-obligations "$o/open-obligations.txt" --extra-fns "lev,sec,conf") ;;
    # kimp and the fixture contract with what a store is (`storeOk`, read by --store-ok) as a part
    # of their kind 1 invariant, whose walk gives the store lemmas of the generated Spec.lean
    kimpni) GEN_ARGS=(--kore "$(kore_dir imp-ni)/definition.kore" --runtime "$(kore_dir imp-ni)/runtime.json"
            --out "$o" --name KImpNI --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant storeOk@env) ;;
    contract) libs_fixture_args "$1"; GEN_ARGS+=(--invariant storeOk@env) ;;
    contractsec) libs_fixture_args "$1"; GEN_ARGS+=(--extra-fns "lev,sec,conf,quiet") ;;
    *) return 1 ;;
  esac
  return 0
}

# ImpNI, ContractNI: `Tr.lean`, the semantics to the checker, translating programs (`--roots`)
relate_noninterference() {
  case $1 in
    ImpNI) na=KImpNI ka=$(kore_dir imp-ni) nb=KImpSec kd=$(kore_dir imp-sec) extra=(--roots "SortStmt,SortExpr") ;;
    ContractNI) na=Contract ka=$(libs_fixture contract) nb=ContractSec kd=$(libs_fixture contractsec)
      extra=(--roots "SortStmt,SortExpr") ;;
    *) return 1 ;;
  esac
}

# libs_noninterference NS: the noninterference scaffold of demo NS (ImpNI: kimp, as kimpni, with
# the checker demos/k/imp-sec.k; ContractNI: the fixture contract, with its checker, the fixture
# contractsec; each needs libs_relate NS for the translation of programs), `NS/NI.lean`, the facts
# its statement is about from the two definitions (`NS/Spec.lean`, by --store-ok), the relation
# generated from the checker (`NS/Levels.lean`, `NS/Stack.lean`, `NS/Proof.lean`, around the hand
# module `NS/Store.lean` and the open list `open.txt`), and its report `NS/noninterference.toml`.
libs_noninterference() {
  case $1 in
    ImpNI) "$G" noninterference --kore "$(kore_dir imp-ni)/definition.kore" --name KImpNI --ns ImpNI \
        --store-cell env --program-sort SortStmt --params "(G : KImpSec.SortMap)" --store-ok storeOk \
        --out "$DEMOS/ImpNI/ImpNI/NI.lean" --report "$DEMOS/ImpNI/noninterference.toml" \
        --checker-kore "$(kore_dir imp-sec)/definition.kore" --checker-name KImpSec --lev lev --sec sec --conf conf \
        --open "$DEMOS/ImpNI/open.txt" --out-dir "$DEMOS/ImpNI/ImpNI" ;;
    # noninterference up to disclosure: the ledger public, the witnesses' answers private, the
    # ledger and the transcript observed, `<disclosed>` the disclosure cell (design.md, section 3.7)
    ContractNI) "$G" noninterference --kore "$(libs_fixture contract)/definition.kore" --name Contract \
        --ns ContractNI --store-cell env --program-sort SortStmt --params "(G : ContractSec.SortMap)" \
        --store-ok storeOk --inputs "LEDGER=public,WIT=private" \
        --observe "ledger,transcript" --disclosed disclosed \
        --out "$DEMOS/ContractNI/ContractNI/NI.lean" --report "$DEMOS/ContractNI/noninterference.toml" \
        --checker-kore "$(libs_fixture contractsec)/definition.kore" --checker-name ContractSec \
        --lev lev --sec sec --conf conf --quiet quiet \
        --open "$DEMOS/ContractNI/open.txt" --out-dir "$DEMOS/ContractNI/ContractNI" ;;
    *) echo "libs_noninterference: unknown demo $1" >&2; return 2 ;;
  esac
}

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

gate_noninterference() {
  # noninterference (docs/design.md, section 3.7): kimp with what a store is (kimpni) and the
  # checker, library impsec built only as far as the demo needs (its functions)
  if runs demo ImpNI; then
    phase "scaffold ImpNI"
    kc imp-ni && kc imp-sec && partlib kimpni KImpNI && partlib impsec KImpSec.Functions
    rel ImpNI
    scaffold noninterference-ImpNI libs_noninterference ImpNI
    dbuild ImpNI
  fi
  # noninterference up to disclosure (section 3.7): the fixture contract, a contract with private
  # state, and its checker, the fixture contractsec (libraries contract, whole, and contractsec,
  # its functions)
  if runs demo ContractNI; then
    phase "scaffold ContractNI"
    partlib contract Contract && partlib contractsec ContractSec.Functions
    rel ContractNI
    scaffold noninterference-ContractNI libs_noninterference ContractNI
    dbuild ContractNI
  fi
}
