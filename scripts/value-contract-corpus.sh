#!/usr/bin/env bash
# The value contract's full-definition gate (V12): the load-time critical-pair check's verdicts
# and counts on whole compiled definitions, compared with scripts/value-contract-corpus.toml.
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
manifest="$workspace/scripts/value-contract-corpus.toml"
work_tree=${CONFORMANCE_WORK_TREE:-/tmp/k-rust-conformance/k-distribution}
wasm_source=${WASM_SEMANTICS_CHECKOUT:-$workspace/wasm-semantics}
builtin=${K_BUILTIN_DIRECTORY:-$workspace/k/k-distribution/include/kframework/builtin}
krust=${KRUST_BIN:-}
work=${VALUE_CONTRACT_WORK:-}
update=false

usage() {
  cat <<'EOF'
usage: scripts/value-contract-corpus.sh [--work-tree DIR] [--wasm-source DIR] [--krust BIN]
                                        [--work DIR] [--update]

Load every definition of scripts/value-contract-corpus.toml with the backend and compare the
load-time critical-pair check's verdict and counts (k_rust_backend::confluence) with the
manifest. Exit status 3 when a value differs, 2 on a usage or setup error.

A definition is either compiled by the conformance driver into the work tree
(`conformance:PATH`, PATH relative to --work-tree, default $CONFORMANCE_WORK_TREE or
/tmp/k-rust-conformance/k-distribution; run scripts/conformance-ratchet.sh on the cases
first), or `wasm`: WASM's test.md, compiled here with --krust (default $KRUST_BIN) from
--wasm-source (default $WASM_SEMANTICS_CHECKOUT or the workspace's wasm-semantics) against
$K_BUILTIN_DIRECTORY (default the workspace's k checkout).

  --work DIR   keep the WASM compilation and the harness output in DIR (default: a temporary
               directory, removed on exit)
  --update     print the manifest with the measured values instead of comparing
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
    --krust) krust=${2:?}; shift 2 ;;
    --work) work=${2:?}; shift 2 ;;
    --update) update=true; shift ;;
    -h | --help) usage; exit 0 ;;
    *) usage >&2; die "unknown argument $1" ;;
  esac
done

if [[ -z $work ]]; then
  work=$(mktemp -d)
  trap 'rm -r -- "$work"' EXIT
fi
mkdir -p "$work"

entries=$(python3 - "$manifest" <<'EOF'
import sys, tomllib
with open(sys.argv[1], "rb") as manifest:
    for case in tomllib.load(manifest)["case"]:
        print(f"{case['name']}\t{case['definition']}")
EOF
)

definitions=()
while IFS=$'\t' read -r name definition; do
  case "$definition" in
    wasm)
      [[ -n $krust ]] || die "the wasm case needs --krust or KRUST_BIN"
      [[ -d $wasm_source ]] || die "no WASM semantics at $wasm_source"
      "$krust" kcompile "$wasm_source/pykwasm/src/pykwasm/kdist/wasm-semantics/test.md" \
        --main-module WASM-TEST --backend rust --output-directory "$work/$name" \
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

python3 - "$manifest" "$work/harness.log" "$update" <<'EOF'
import json, sys, tomllib

manifest_path, log_path, update = sys.argv[1], sys.argv[2], sys.argv[3] == "true"
with open(manifest_path, "rb") as manifest:
    cases = tomllib.load(manifest)["case"]
measured = {}
with open(log_path) as log:
    for line in log:
        if line.startswith("VALUE_CONTRACT "):
            row = json.loads(line[len("VALUE_CONTRACT "):])
            measured[row["name"]] = row
keys = ["equations", "pairs", "overlaps", "separated", "refuted", "joined", "unjoined",
        "relevant", "violations", "heads", "tainted_heads", "tainted_symbols", "several_matches",
        "families", "confluent_families", "relevant_equations", "skipped", "full_pairs",
        "full_unjoined", "full_tainted_symbols"]
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
