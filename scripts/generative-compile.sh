#!/usr/bin/env bash
# Generative compile test: an opt-in tool, not part of `cargo test`, CI, or any gate.
#
# Generates COUNT small K definitions from SEED (scripts/generative/gen.py), compiles each with
# the release harness crates/k-rust/examples/generative-compile.rs, loads every emitted
# definition.kore in the Rust backend, and triages the results (scripts/generative/triage.py).
# A row is unexpected when it is a panic, crash, timeout, KORE parse or backend failure after a
# successful compilation, an error located in a builtin source, or a rejection that no category
# of scripts/generative/expected.toml explains as invalid input. Exits 1 when any row is
# unexpected, 2 on a usage or build error, 0 otherwise.
#
# Cost: the first build compiles the example and its feature combination (about a minute with
# cached dependencies); a run takes about 0.3 s of CPU per case, so the default 1000 cases take
# about 40 s of wall time with 8 jobs. Each worker runs under a 6 GiB address-space limit.
# The corpus is not kept: the same --seed and --count regenerate it. On unexpected rows the work
# directory (corpus/, results.tsv) is kept and its path printed; --keep DIR always keeps it there.
# Reduce a case with scripts/generative/reduce.py.
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
generative="$workspace/scripts/generative"
count=1000
seed=1
jobs=8
timeout=10
fresh=false
keep=
features=cli,kompile-invariant-checks,generative-harness

usage() {
  cat <<'EOF'
usage: scripts/generative-compile.sh [--count N] [--seed S] [--jobs J] [OPTIONS]

  --count N       cases to generate (default 1000)
  --seed S        generator seed (default 1)
  --jobs J        parallel worker processes (default 8)
  --timeout SECS  per-case limit (default 10)
  --fresh         reload the prelude for every case instead of compiling against a prelude
                  loaded once per worker; about twice the cost per case, and needed to see a case
                  whose syntax changes how builtin rules parse
  --keep DIR      write the corpus and results.tsv to DIR and keep them
  --gh-release    build with the z3-inference-gh-release feature (downloads Z3)
EOF
}

die() {
  echo "error: $*" >&2
  exit 2
}

while (( $# > 0 )); do
  case $1 in
    --count) [[ $# -ge 2 && $2 =~ ^[1-9][0-9]*$ ]] || die "--count needs a positive integer"; count=$2; shift 2 ;;
    --seed) [[ $# -ge 2 && $2 =~ ^[0-9]+$ ]] || die "--seed needs a non-negative integer"; seed=$2; shift 2 ;;
    --jobs) [[ $# -ge 2 && $2 =~ ^[1-9][0-9]*$ ]] || die "--jobs needs a positive integer"; jobs=$2; shift 2 ;;
    --timeout) [[ $# -ge 2 && $2 =~ ^[0-9]+(\.[0-9]+)?$ ]] || die "--timeout needs a number of seconds"; timeout=$2; shift 2 ;;
    --fresh) fresh=true; shift ;;
    --keep) [[ $# -ge 2 ]] || die "--keep needs a directory"; keep=$2; shift 2 ;;
    --gh-release) features+=,z3-inference-gh-release; shift ;;
    -h|--help) usage; exit 0 ;;
    *) usage >&2; exit 2 ;;
  esac
done

command -v cargo >/dev/null || die "cargo is required to build the harness"
command -v python3 >/dev/null || die "python3 is required"

echo "building the generative-compile harness (features $features)" >&2
cargo build --quiet --release --locked --manifest-path "$workspace/Cargo.toml" \
  -p k-rust --no-default-features --features "$features" --example generative-compile \
  || die "harness build failed"
target_dir=$(cargo metadata --no-deps --format-version 1 --manifest-path "$workspace/Cargo.toml" \
  | python3 -c 'import json, sys; print(json.load(sys.stdin)["target_directory"])')
harness="$target_dir/release/examples/generative-compile"
[[ -x "$harness" ]] || die "harness binary is missing: $harness"

if [[ -n "$keep" ]]; then
  mkdir -p "$keep"
  work=$(cd "$keep" && pwd)
  rm -rf "$work/corpus" "$work/results.tsv"
else
  work=$(mktemp -d "${TMPDIR:-/tmp}/generative-compile.XXXXXX")
fi

python3 "$generative/gen.py" "$work/corpus" --count "$count" --seed "$seed"
run_args=(run "$work/corpus" "$work/results.tsv" --jobs "$jobs" --timeout "$timeout")
if [[ $fresh == true ]]; then
  run_args+=(--fresh)
fi
"$harness" "${run_args[@]}"

status=0
python3 "$generative/triage.py" "$work/results.tsv" "$work/corpus" || status=$?
if (( status == 0 )) && [[ -z "$keep" ]]; then
  rm -rf "$work"
else
  echo "corpus and results kept in $work" >&2
fi
exit "$status"
