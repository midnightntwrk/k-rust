#!/usr/bin/env bash
# The value contract's full-definition gate (V12): the load-time critical-pair check's verdicts
# and counts on whole compiled definitions, compared with scripts/value-contract-corpus.toml.
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
manifest="$workspace/scripts/value-contract-corpus.toml"
work_tree=${CONFORMANCE_WORK_TREE:-/tmp/k-rust-conformance/k-distribution}
wasm_source=${WASM_SEMANTICS_CHECKOUT:-$workspace/wasm-semantics}
evm_source=${EVM_SEMANTICS_CHECKOUT:-$workspace/evm-semantics}
builtin=${K_BUILTIN_DIRECTORY:-$workspace/k/k-distribution/include/kframework/builtin}
krust=${KRUST_BIN:-}
work=${VALUE_CONTRACT_WORK:-}
update=false
cases=()

usage() {
  cat <<'EOF'
usage: scripts/value-contract-corpus.sh [--work-tree DIR] [--wasm-source DIR] [--evm-source DIR]
                                        [--krust BIN] [--work DIR] [--update] [CASE...]

Load the definitions of scripts/value-contract-corpus.toml (the named CASEs, default every case)
with the backend and compare the load-time critical-pair check's verdict and counts
(k_rust_backend::confluence) with the manifest. Exit status 3 when a value differs or a case has
no recorded values, 2 on a usage or setup error (an unknown CASE included).

A definition is either compiled by the conformance driver into the work tree
(`conformance:PATH`, PATH relative to --work-tree, default $CONFORMANCE_WORK_TREE or
/tmp/k-rust-conformance/k-distribution; scripts/conformance-ratchet.sh runs this script on the
cases it compiled), or compiled here against $K_BUILTIN_DIRECTORY (default the workspace's k
checkout) with --krust (default $KRUST_BIN, otherwise the reference gates' krust build):
  wasm  WASM's test.md, from --wasm-source (default $WASM_SEMANTICS_CHECKOUT or the
        workspace's wasm-semantics);
  kevm  KEVM's optimizations.md at module EVM-OPTIMIZATIONS, the evm-equivalence case of the
        compile gate, from --evm-source (default $EVM_SEMANTICS_CHECKOUT or the workspace's
        evm-semantics).

  --work DIR   keep the compilations and the harness output in DIR (default: a temporary
               directory, removed on exit)
  --update     print the selected cases with the measured values instead of comparing
EOF
}

die() {
  echo "error: $*" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --work-tree) work_tree=${2:?}; shift 2 ;;
    --wasm-source) wasm_source=${2:?}; shift 2 ;;
    --evm-source) evm_source=${2:?}; shift 2 ;;
    --krust) krust=${2:?}; shift 2 ;;
    --work) work=${2:?}; shift 2 ;;
    --update) update=true; shift ;;
    -h | --help) usage; exit 0 ;;
    -*) usage >&2; die "unknown argument $1" ;;
    *) cases+=("$1"); shift ;;
  esac
done

if [[ -z $work ]]; then
  work=$(mktemp -d)
  trap 'rm -r -- "$work"' EXIT
fi
mkdir -p "$work"

entries=$(python3 - "$manifest" "${cases[@]}" <<'EOF'
import sys, tomllib
with open(sys.argv[1], "rb") as manifest:
    known = {case["name"]: case["definition"] for case in tomllib.load(manifest)["case"]}
selected = sys.argv[2:] or list(known)
unknown = [name for name in selected if name not in known]
if unknown:
    sys.exit(f"error: unknown case {' '.join(unknown)}; cases: {' '.join(known)}")
for name in selected:
    print(f"{name}\t{known[name]}")
EOF
) || exit 2

# krust for the definitions compiled here: --krust, or the reference gates' release build.
need_krust() {
  [[ -z $krust ]] || return 0
  # shellcheck source=scripts/reference-memory-guard.sh
  source "$workspace/scripts/reference-memory-guard.sh"
  reference_announce_krust_gate_build
  cargo build --quiet --release "${krust_gate_cargo_args[@]}" --manifest-path "$workspace/Cargo.toml" \
    -p k-rust --bin krust || die "building krust failed"
  krust=$krust_gate_binary
}

definitions=()
while IFS=$'\t' read -r name definition; do
  case "$definition" in
    wasm)
      [[ -d $wasm_source ]] || die "no WASM semantics at $wasm_source"
      need_krust
      "$krust" kcompile "$wasm_source/pykwasm/src/pykwasm/kdist/wasm-semantics/test.md" \
        --main-module WASM-TEST --backend rust --output-directory "$work/$name" \
        --md-selector "k & ! concrete" --builtin-directory "$builtin" </dev/null \
        >"$work/$name.kcompile.log" 2>&1 \
        || die "compiling $name failed; see $work/$name.kcompile.log"
      definitions+=("$name=$work/$name/definition.kore")
      ;;
    kevm)
      [[ -d $evm_source ]] || die "no KEVM semantics at $evm_source"
      need_krust
      "$krust" kcompile "$evm_source/kevm-pyk/src/kevm_pyk/kproj/evm-semantics/optimizations.md" \
        --main-module EVM-OPTIMIZATIONS --backend rust --output-directory "$work/$name" \
        -I "$evm_source/kevm-pyk/src/kevm_pyk/kproj/plugin" --hook-namespaces "JSON KRYPTO" \
        --md-selector "k & ! concrete" --builtin-directory "$builtin" </dev/null \
        >"$work/$name.kcompile.log" 2>&1 \
        || die "compiling $name failed; see $work/$name.kcompile.log"
      definitions+=("$name=$work/$name/definition.kore")
      ;;
    conformance:*)
      path="$work_tree/${definition#conformance:}"
      [[ -f $path ]] || die "$name: no compiled definition at $path"
      definitions+=("$name=$path")
      ;;
    *) die "$name: unknown definition kind $definition" ;;
  esac
done <<<"$entries"

joined=$(IFS=:; echo "${definitions[*]}")
(
  cd "$workspace"
  VALUE_CONTRACT_DEFINITIONS=$joined cargo test --release --locked -p k-rust-backend \
    --test value_contract_corpus -- --ignored --nocapture
) >"$work/harness.log" 2>&1 || die "the harness failed; see $work/harness.log"

python3 - "$manifest" "$work/harness.log" "$update" "${cases[@]}" <<'EOF'
import json, sys, tomllib

manifest_path, log_path, update = sys.argv[1], sys.argv[2], sys.argv[3] == "true"
with open(manifest_path, "rb") as manifest:
    cases = tomllib.load(manifest)["case"]
if sys.argv[4:]:
    cases = [case for case in cases if case["name"] in sys.argv[4:]]
measured = {}
with open(log_path) as log:
    for line in log:
        if line.startswith("VALUE_CONTRACT "):
            row = json.loads(line[len("VALUE_CONTRACT "):])
            measured[row["name"]] = row
keys = ["equations", "pairs", "overlaps", "separated", "refuted", "joined", "unjoined",
        "relevant", "violations", "heads", "tainted_heads", "tainted_symbols", "several_matches",
        "families", "confluent_families", "relevant_equations", "skipped", "full_pairs",
        "full_unjoined", "full_tainted_symbols", "simplifier_calls", "condition_memo_hits",
        "full_simplifier_calls", "full_condition_memo_hits", "condition_memo_refusals",
        "full_condition_memo_refusals", "condition_budget_stops", "condition_stack_stops",
        "full_condition_budget_stops", "full_condition_stack_stops"]
if update:
    for case in cases:
        row = measured[case["name"]]
        print("[[case]]")
        print(f'name = "{case["name"]}"')
        print(f'definition = "{case["definition"]}"')
        print("[case.expected]")
        for key in keys:
            print(f"{key} = {row[key]}")
        print()
    sys.exit(0)
mismatches = 0
for case in cases:
    row = measured.get(case["name"])
    if row is None:
        print(f'{case["name"]}: not measured')
        mismatches += 1
        continue
    if not case.get("expected"):
        print(f'{case["name"]}: no recorded values; record them with --update {case["name"]}')
        mismatches += 1
        continue
    differing = [
        f"{key} {expected} -> {row[key]}"
        for key, expected in case["expected"].items()
        if row[key] != expected
    ]
    status = "ok" if not differing else "DIFFERS: " + ", ".join(differing)
    print(f'{case["name"]}: {row["relevant"]} relevant non-joined pairs, '
          f'{row["tainted_heads"]} of {row["heads"]} heads withdrawn, '
          f'load {row["load_seconds"]:.3f} s; {status}')
    mismatches += bool(differing)
sys.exit(3 if mismatches else 0)
EOF
