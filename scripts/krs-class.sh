#!/usr/bin/env bash
# The class tests' full tier, gate krs-class (krs/crates/krs-cli/tests/class_matrix.rs): every case
# that krs_test_support::class_matrix generates, through Cargo, rustc, the collector and emit-k's
# lowering, judged by the table-free invariants and krs/tests/class-matrix/expected.toml, and each
# accepted case's definition judged as `krs check` judges it on the native routes (K6) and its
# program run on that compile (K7), with the known failures in krs/tests/class-matrix/pending.toml.
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
all_shards=(readable cells init terms import notation k4 k5)

usage() {
  cat <<EOF
usage: scripts/krs-class.sh [--workers N] [--shard NAME]... [--record]

Run the shards of krs/crates/krs-cli/tests/class_matrix.rs (every shard by default; NAME is one of
${all_shards[*]}). Each worker builds the batch packages of its cases in a Cargo target of its own,
reused across its batches; --workers defaults to what the host's memory has room for now: the
available memory over 3 GiB, at least 1 and at most the CPU count (or the cgroup's quota). CPU load
is not consulted: it fluctuates far more than memory, and an oversubscribed CPU only slows a run. The workers' targets and packages live in one scratch
directory, removed when the run ends, failure included. KRS_CLASS_TARGET_DIR selects the target the
test binary is built in (default target/gates), KRS_CLASS_OUT a directory for one TSV line per case
and the pending entries of each unrecorded deviation (see the test's documentation). --record writes
the K of every accepted case that no refusal rule covers into krs/tests/class-matrix/expected.toml,
a term family's case (terms/.., import/.., notation/..) into krs/tests/class-matrix/accepted-terms.toml, for
review as a diff. KRS_CLASS_NATIVE=0 skips K6 and KRS_CLASS_NATIVE=alone judges each accepted case
alone (KRS_CLASS_CLOSURE=0 skips K3); KRS_CLASS_RUN=0 skips K7, which runs on K6's compile, and
KRS_CLASS_RUN_SECONDS is its time limit per program (default 60). K6 compiles natively,
as \`krs check\` does, so the test links the Z3 release krs/Krs.lock pins, found through KRS_Z3_LIB
or the Nix store (KRS_NIX_STORE, default /nix/store). Exit status 0
when every case conforms or is pending as recorded, 1 otherwise, 2 on a usage error.
EOF
}

workers=
record=
shards=()
while (($#)); do
  case $1 in
    -h | --help)
      usage
      exit 0
      ;;
    --workers)
      [[ ${2:-} =~ ^[1-9][0-9]*$ ]] || { usage >&2; exit 2; }
      workers=$2
      shift 2
      ;;
    --record)
      record=1
      shift
      ;;
    --shard)
      [[ " ${all_shards[*]} " == *" ${2:-} "* ]] || { usage >&2; exit 2; }
      shards+=("$2")
      shift 2
      ;;
    *)
      usage >&2
      exit 2
      ;;
  esac
done
((${#shards[@]})) || shards=("${all_shards[@]}")

# The CPUs this process may use: the cgroup's quota when it sets one, the CPU count otherwise.
cpus() {
  local quota period
  if read -r quota period 2>/dev/null </sys/fs/cgroup/cpu.max && [[ $quota != max ]]; then
    echo $(((quota + period - 1) / period))
  else
    nproc
  fi
}

if [[ -z $workers ]]; then
  available_kib=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
  workers=$((available_kib / (3 * 1024 * 1024)))
  limit=$(cpus)
  ((workers <= limit)) || workers=$limit
  ((workers >= 1)) || workers=1
  echo "[krs-class] $workers workers ($((available_kib / 1024 / 1024)) GiB available)" >&2
fi

# The test removes the scratch of a run whose owner (owner.pid) is gone, an interrupted one.
scratch=$(mktemp -d "${TMPDIR:-/tmp}/krs-class-XXXXXX")
echo $$ >"$scratch/owner.pid"
report_and_remove() {
  echo "[krs-class] scratch at its end: $(du -sh "$scratch" 2>/dev/null | cut -f1)" >&2
  rm -rf "$scratch"
}
trap report_and_remove EXIT

# K6 judges what `krs check` judges, k-rust's native compile included, so the test builds with the
# solver profile krs/Krs.lock pins and links its Z3 release, as the other KRS gates do
# (krs/tests/support/tools.py, z3_library_dir).
z3_version=$(awk -F'"' '/^\[solver\]/ { solver = 1 } solver && /^version/ { print $2; exit }' \
  "$workspace/krs/Krs.lock")
z3_lib=
for candidate in ${KRS_Z3_LIB:+"$KRS_Z3_LIB" "$KRS_Z3_LIB/lib"} \
  "${KRS_NIX_STORE:-/nix/store}"/*-z3-"$z3_version"-lib/lib; do
  if [[ -f $candidate/libz3.so ]]; then
    z3_lib=$candidate
    break
  fi
done
if [[ -z $z3_lib ]]; then
  echo "[krs-class] Z3 $z3_version was not found; set KRS_Z3_LIB to its shared-library directory" >&2
  exit 2
fi
export LIBRARY_PATH=$z3_lib${LIBRARY_PATH:+:$LIBRARY_PATH}
export LD_LIBRARY_PATH=$z3_lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}

KRS_CLASS_WORKERS=$workers KRS_CLASS_SCRATCH=$scratch KRS_CLASS_RECORD=$record RUSTC_WRAPPER='' \
  cargo test --locked --manifest-path "$workspace/Cargo.toml" \
  --target-dir "${KRS_CLASS_TARGET_DIR:-$workspace/target/gates}" \
  -p krs-cli --no-default-features --features z3-inference --test class_matrix -- \
  --ignored --exact --test-threads=1 --show-output "${shards[@]}"
