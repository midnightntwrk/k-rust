# shellcheck shell=bash
# The noninterference area: `noninterference` (ImpNI: kimp with the security checker
# demos/k/imp-sec.k, library impsec, over kimpni, kimp with what a store is, demos/k/imp-ni.k;
# ContractNI: the fixture contract, a contract with private state, with its checker, the fixture
# contractsec; with priority ranks, ImpOwiseNI and ContractOwiseNI: the same with `owise` rules,
# tests/kimp-owise.py and tests/contract-owise.py, libraries kimpowni and contractow; with cells
# observed by equality and no disclosure cell, ImpOutNI: kimp with `print` to a plain cell,
# tests/kimp-print.py, its checker tests/imp-sec-print.py, libraries kimpoutni and impsecp, and
# ContractObsNI: the fixture contract with a checker that releases nothing,
# tests/contractsec-norelease.py, library contractsecnr; with a related store input beside the
# disclosure cell, ContractEnvNI: the fixture contract with `<env> $ENV:Map </env>`,
# tests/contract-env.py, library contractenv). Registry: noninterference.py.

kore_noninterference() {
  case $1 in
    imp-sec) f=$DEMOS/k/imp-sec.k m=IMP-SEC s=IMP-SEC-SYNTAX inc=$KIMP ;;
    imp-ni) f=$DEMOS/k/imp-ni.k m=IMP-NI s=IMP-SYNTAX inc=$KIMP ;;
    # kimp with `owise` rules (tests/kimp-owise.py: `&&`, `||` and the two-armed `if`, priority
    # 200 after the default 50) and what a store is, demos/k/imp-ni.k over it
    imp-owise-ni) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/kimp-owise.py" "$KIMP" "$2.src" || return 2
      f=$DEMOS/k/imp-ni.k m=IMP-NI s=IMP-SYNTAX inc=$2.src ;;
    # the fixture contract with `owise` rules (tests/contract-owise.py: the two-armed `if` and
    # `repeat`'s end)
    contract-owise) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/contract-owise.py" "$FIXTURES/contract/contract.k" "$2.src/contract.k" || return 2
      f=$2.src/contract.k m=CONTRACT s=CONTRACT-SYNTAX inc=$2.src ;;
    # kimp with `print ( E ) ;` appending to a plain `<output>` cell (tests/kimp-print.py, plain)
    # and what a store is, demos/k/imp-ni.k over it; its checker, demos/k/imp-sec.k with `print`
    # (tests/imp-sec-print.py), over the same sources
    imp-out-ni) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/kimp-print.py" "$KIMP" "$2.src" plain || return 2
      f=$DEMOS/k/imp-ni.k m=IMP-NI s=IMP-SYNTAX inc=$2.src ;;
    imp-sec-print) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/kimp-print.py" "$KIMP" "$2.src" plain &&
      python3 -I "$LIBS_DIR/imp-sec-print.py" "$DEMOS/k/imp-sec.k" "$2.src/imp-sec.k" || return 2
      f=$2.src/imp-sec.k m=IMP-SEC s=IMP-SEC-SYNTAX inc=$2.src ;;
    # the fixture contract's checker with no release (tests/contractsec-norelease.py)
    contractsec-norelease) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/contractsec-norelease.py" "$FIXTURES/contractsec/contractsec.k" "$2.src/contractsec.k" || return 2
      f=$2.src/contractsec.k m=CONTRACTSEC s=CONTRACTSEC-SYNTAX inc=$FIXTURES/contract ;;
    # the fixture contract with its store an input (tests/contract-env.py)
    contract-env) mkdir -p "$2.src" &&
      python3 -I "$LIBS_DIR/contract-env.py" "$FIXTURES/contract/contract.k" "$2.src/contract.k" || return 2
      f=$2.src/contract.k m=CONTRACT s=CONTRACT-SYNTAX inc=$2.src ;;
    *) return 1 ;;
  esac
}

name_noninterference() {
  case $1 in
    impsec) echo KImpSec ;;
    kimpni) echo KImpNI ;;
    contract) echo Contract ;;
    contractsec) echo ContractSec ;;
    kimpowni) echo KImpOwNI ;;
    contractow) echo ContractOw ;;
    kimpoutni) echo KImpOutNI ;;
    impsecp) echo KImpSecP ;;
    contractsecnr) echo ContractSecNR ;;
    contractenv) echo ContractEnv ;;
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
    # the same with `owise` rules: three priority ranks (kimp's 50 and 200) and two (contract's)
    kimpowni) GEN_ARGS=(--kore "$(kore_dir imp-owise-ni)/definition.kore" --runtime "$(kore_dir imp-owise-ni)/runtime.json"
            --out "$o" --name KImpOwNI --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant storeOk@env) ;;
    contractow) GEN_ARGS=(--kore "$(kore_dir contract-owise)/definition.kore" --runtime "$(kore_dir contract-owise)/runtime.json"
            --out "$o" --name ContractOw --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant storeOk@env) ;;
    kimpoutni) GEN_ARGS=(--kore "$(kore_dir imp-out-ni)/definition.kore" --runtime "$(kore_dir imp-out-ni)/runtime.json"
            --out "$o" --name KImpOutNI --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant storeOk@env) ;;
    impsecp) GEN_ARGS=(--kore "$(kore_dir imp-sec-print)/definition.kore" --runtime "$(kore_dir imp-sec-print)/runtime.json"
            --out "$o" --name KImpSecP --prelude ../../lean
            --open-obligations "$o/open-obligations.txt" --extra-fns "lev,sec,conf") ;;
    contractsecnr) GEN_ARGS=(--kore "$(kore_dir contractsec-norelease)/definition.kore"
            --runtime "$(kore_dir contractsec-norelease)/runtime.json"
            --out "$o" --name ContractSecNR --prelude ../../lean
            --open-obligations "$o/open-obligations.txt" --extra-fns "lev,sec,conf,quiet") ;;
    contractenv) GEN_ARGS=(--kore "$(kore_dir contract-env)/definition.kore" --runtime "$(kore_dir contract-env)/runtime.json"
            --out "$o" --name ContractEnv --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant storeOk@env) ;;
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
    ImpOwiseNI) na=KImpOwNI ka=$(kore_dir imp-owise-ni) nb=KImpSec kd=$(kore_dir imp-sec) extra=(--roots "SortStmt,SortExpr") ;;
    ContractOwiseNI) na=ContractOw ka=$(kore_dir contract-owise) nb=ContractSec kd=$(libs_fixture contractsec)
      extra=(--roots "SortStmt,SortExpr") ;;
    ImpOutNI) na=KImpOutNI ka=$(kore_dir imp-out-ni) nb=KImpSecP kd=$(kore_dir imp-sec-print) extra=(--roots "SortStmt,SortExpr") ;;
    ContractObsNI) na=Contract ka=$(libs_fixture contract) nb=ContractSecNR kd=$(kore_dir contractsec-norelease)
      extra=(--roots "SortStmt,SortExpr") ;;
    ContractEnvNI) na=ContractEnv ka=$(kore_dir contract-env) nb=ContractSec kd=$(libs_fixture contractsec)
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
    # with priority ranks: ImpNI's and ContractNI's commands over the definitions with `owise` rules
    ImpOwiseNI) "$G" noninterference --kore "$(kore_dir imp-owise-ni)/definition.kore" --name KImpOwNI --ns ImpOwiseNI \
        --store-cell env --program-sort SortStmt --params "(G : KImpSec.SortMap)" --store-ok storeOk \
        --out "$DEMOS/ImpOwiseNI/ImpOwiseNI/NI.lean" --report "$DEMOS/ImpOwiseNI/noninterference.toml" \
        --checker-kore "$(kore_dir imp-sec)/definition.kore" --checker-name KImpSec --lev lev --sec sec --conf conf \
        --open "$DEMOS/ImpOwiseNI/open.txt" --out-dir "$DEMOS/ImpOwiseNI/ImpOwiseNI" ;;
    ContractOwiseNI) "$G" noninterference --kore "$(kore_dir contract-owise)/definition.kore" --name ContractOw \
        --ns ContractOwiseNI --store-cell env --program-sort SortStmt --params "(G : ContractSec.SortMap)" \
        --store-ok storeOk --inputs "LEDGER=public,WIT=private" \
        --observe "ledger,transcript" --disclosed disclosed \
        --out "$DEMOS/ContractOwiseNI/ContractOwiseNI/NI.lean" --report "$DEMOS/ContractOwiseNI/noninterference.toml" \
        --checker-kore "$(libs_fixture contractsec)/definition.kore" --checker-name ContractSec \
        --lev lev --sec sec --conf conf --quiet quiet \
        --open "$DEMOS/ContractOwiseNI/open.txt" --out-dir "$DEMOS/ContractOwiseNI/ContractOwiseNI" ;;
    # cells observed by equality, no disclosure cell (design.md, section 3.7): ImpNI's store and
    # kimp's `<output>`; the contract's ledger, transcript and disclosed values, nothing released
    ImpOutNI) "$G" noninterference --kore "$(kore_dir imp-out-ni)/definition.kore" --name KImpOutNI --ns ImpOutNI \
        --store-cell env --program-sort SortStmt --params "(G : KImpSecP.SortMap)" --store-ok storeOk \
        --observe "env=lowEq G,output" \
        --out "$DEMOS/ImpOutNI/ImpOutNI/NI.lean" --report "$DEMOS/ImpOutNI/noninterference.toml" \
        --checker-kore "$(kore_dir imp-sec-print)/definition.kore" --checker-name KImpSecP --lev lev --sec sec --conf conf \
        --open "$DEMOS/ImpOutNI/open.txt" --out-dir "$DEMOS/ImpOutNI/ImpOutNI" ;;
    ContractObsNI) "$G" noninterference --kore "$(libs_fixture contract)/definition.kore" --name Contract \
        --ns ContractObsNI --store-cell env --program-sort SortStmt --params "(G : ContractSecNR.SortMap)" \
        --store-ok storeOk --inputs "LEDGER=public,WIT=private" \
        --observe "ledger,transcript,disclosed" \
        --out "$DEMOS/ContractObsNI/ContractObsNI/NI.lean" --report "$DEMOS/ContractObsNI/noninterference.toml" \
        --checker-kore "$(kore_dir contractsec-norelease)/definition.kore" --checker-name ContractSecNR \
        --lev lev --sec sec --conf conf --quiet quiet \
        --open "$DEMOS/ContractObsNI/open.txt" --out-dir "$DEMOS/ContractObsNI/ContractObsNI" ;;
    # a related store input beside the disclosure cell (design.md, section 3.7): the fixture
    # contract with its store an input, the stores related and observed by `lowEq G`
    ContractEnvNI) "$G" noninterference --kore "$(kore_dir contract-env)/definition.kore" --name ContractEnv \
        --ns ContractEnvNI --store-cell env --program-sort SortStmt --params "(G : ContractSec.SortMap)" \
        --store-ok storeOk --inputs "ENV=lowEq G,LEDGER=public,WIT=private" \
        --observe "env=lowEq G,ledger,transcript" --disclosed disclosed \
        --out "$DEMOS/ContractEnvNI/ContractEnvNI/NI.lean" --report "$DEMOS/ContractEnvNI/noninterference.toml" \
        --checker-kore "$(libs_fixture contractsec)/definition.kore" --checker-name ContractSec \
        --lev lev --sec sec --conf conf --quiet quiet \
        --open "$DEMOS/ContractEnvNI/open.txt" --out-dir "$DEMOS/ContractEnvNI/ContractEnvNI" ;;
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
  # with priority ranks (section 3.7): ImpNI and ContractNI over the definitions with `owise` rules
  if runs demo ImpOwiseNI; then
    phase "scaffold ImpOwiseNI"
    kc imp-owise-ni && kc imp-sec && partlib kimpowni KImpOwNI && partlib impsec KImpSec.Functions
    rel ImpOwiseNI
    scaffold noninterference-ImpOwiseNI libs_noninterference ImpOwiseNI
    dbuild ImpOwiseNI
  fi
  if runs demo ContractOwiseNI; then
    phase "scaffold ContractOwiseNI"
    kc contract-owise && partlib contractow ContractOw && partlib contractsec ContractSec.Functions
    rel ContractOwiseNI
    scaffold noninterference-ContractOwiseNI libs_noninterference ContractOwiseNI
    dbuild ContractOwiseNI
  fi
  # cells observed by equality without a disclosure cell (section 3.7): kimp with `print` to a
  # plain cell, and the fixture contract under a checker that releases nothing
  if runs demo ImpOutNI; then
    phase "scaffold ImpOutNI"
    kc imp-out-ni && kc imp-sec-print && partlib kimpoutni KImpOutNI && partlib impsecp KImpSecP.Functions
    rel ImpOutNI
    scaffold noninterference-ImpOutNI libs_noninterference ImpOutNI
    dbuild ImpOutNI
  fi
  if runs demo ContractObsNI; then
    phase "scaffold ContractObsNI"
    kc contractsec-norelease && partlib contract Contract && partlib contractsecnr ContractSecNR.Functions
    rel ContractObsNI
    scaffold noninterference-ContractObsNI libs_noninterference ContractObsNI
    dbuild ContractObsNI
  fi
  # a related store input beside the disclosure cell (section 3.7): the fixture contract with its
  # store an input (tests/contract-env.py, library contractenv), the fixture checker contractsec
  if runs demo ContractEnvNI; then
    phase "scaffold ContractEnvNI"
    kc contract-env && partlib contractenv ContractEnv && partlib contractsec ContractSec.Functions
    rel ContractEnvNI
    scaffold noninterference-ContractEnvNI libs_noninterference ContractEnvNI
    dbuild ContractEnvNI
  fi
}
