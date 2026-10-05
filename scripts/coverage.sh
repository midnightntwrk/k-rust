#!/usr/bin/env bash
set -euo pipefail

# Measure which production lines of the workspace the Rust test suites execute.
#
# A manual check, not a gate: run it before removing tests or restructuring a suite, to see
# what the change would stop executing, and now and then to follow the trend. It takes about
# 20 minutes on 8 jobs and needs about 55 GB of disk below --work: 41 GB for the
# instrumented build and 12 GB of raw profiles, which are deleted at the end unless kept.
#
# Usage: scripts/coverage.sh [--work DIR] [--jobs N] [--no-portable] [--no-per-test]
#                            [--keep-profiles] [--analyze-only]
#                            [-- NEXTEST-RUN-ARGUMENTS]
#
#   --work DIR        Work and report directory (default: target/coverage-suite). Its
#                     profiles/, export/ and report/ are replaced; cargo-target/ is kept, so a
#                     second run rebuilds only what changed.
#   --jobs N          Build jobs, nextest test threads and export processes (default: 8).
#   --no-portable     Skip the portable suite.
#   --no-per-test     Skip the per-test export (and with it the per-test and per-card test
#                     columns), which is the slowest part of the analysis.
#   --keep-profiles   Keep the raw profiles and merged profile data.
#   --analyze-only    Analyze the profiles that an earlier run with --keep-profiles kept,
#                     without building or running tests.
#   -- ARGUMENTS      Passed to every `cargo nextest run`, as a filter: `-- -E 'binary(cli)'`.
#
# It runs two suites with an instrumented build (`-C instrument-coverage`):
#
#   z3        cargo nextest run --workspace --no-default-features
#                --features k-rust/cli,k-rust/z3-inference
#   portable  cargo nextest run -p k-rust -p k-rust-wasm --no-default-features
#
# Doc-tests and the Node and WebAssembly `npm test` suites are not measured, nor are the CLI
# scripts (reference differentials, backend-smoke, generative-compile).
#
# Each test runs under scripts/coverage/runner.sh, a cargo target runner that sends the
# profiles of the test and of every process it starts (each krust, a rerun of its own binary)
# to profiles/SUITE/BINARY/TEST. The profiles are written in continuous mode
# (`-C llvm-args=-runtime-counter-relocation` and `%c` in LLVM_PROFILE_FILE), so a process
# that is killed, such as a krust child that a watchdog stops, keeps its counters. Build
# scripts and procedural macros are instrumented as well; LLVM_PROFILE_FILE is set during the
# builds so that their profiles land in profiles/build rather than in the checkout or the
# Cargo registry sources.
#
# The analysis (scripts/coverage/collect.py, report.py) merges the profiles per binary and
# per test, exports them with llvm-cov, drops test code (tests/ and src/tests/ files,
# `#[cfg(test)]` items), and writes report/:
#
#   summary.md     executed lines per suite and per crate, split into unit tests, integration
#                  tests and krust processes, and any profile that could not be attributed
#   files.md       the files with the most unexecuted lines
#   cards.md       per algorithm card (from `algo-graph graph`): executed lines of its sites
#                  per suite, the tests that execute a site, and those in the site's module
#   tests.tsv      per test: production lines executed, and lines no other test executes
#   uncovered.txt  unexecuted production lines as file:first-last
#
# A line counts when it appears in the llvm-cov export of a binary built for a suite, including
# a test binary that ran no test; the denominator is the union over both suites.
#
# Line coverage says what ran, not what was checked. A line that one test alone executes may
# be asserted by none, and a line that exactly two tests execute is unique to neither. Card
# site spans come from a brace-matching scanner (scripts/coverage/source.py), not a
# Rust parser; cards.md lists any site it could not find.
#
# Requirements: cargo-nextest, python3 3.11 or later, readelf, and llvm-profdata and llvm-cov
# from the active toolchain's llvm-tools component (`rustup component add llvm-tools`), or
# LLVM_TOOLS naming a directory that holds them. The suites build with the z3-inference
# feature, which needs Z3 the same way an ordinary build of that feature does. RUSTFLAGS and
# CARGO_TARGET_DIR are set by the script.
#
# A failing test does not stop the run, since its profile still counts; the script exits
# nonzero when a suite failed or a profile could not be attributed.

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
work="$workspace/target/coverage-suite"
jobs=8
portable=1
per_test=1
keep=0
analyze_only=0
run_arguments=()

usage() {
  sed -n '4,25p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

while (($#)); do
  case "$1" in
    --work) work=${2:?}; shift 2 ;;
    --jobs) jobs=${2:?}; shift 2 ;;
    --no-portable) portable=0; shift ;;
    --no-per-test) per_test=0; shift ;;
    --keep-profiles) keep=1; shift ;;
    --analyze-only) analyze_only=1; keep=1; shift ;;
    -h|--help) usage; exit 0 ;;
    --) shift; run_arguments=("$@"); break ;;
    *) echo "error: unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

LLVM_TOOLS=${LLVM_TOOLS:-"$(rustc --print sysroot)/lib/rustlib/$(rustc -vV | sed -n 's/^host: //p')/bin"}
for tool in llvm-profdata llvm-cov; do
  [[ -x "$LLVM_TOOLS/$tool" ]] || { echo "error: $LLVM_TOOLS/$tool is missing (rustup component add llvm-tools)" >&2; exit 2; }
done
cargo nextest --version >/dev/null 2>&1 || { echo "error: cargo-nextest is required" >&2; exit 2; }
command -v readelf >/dev/null || { echo "error: readelf is required" >&2; exit 2; }
python3 -c 'import sys, tomllib; sys.exit(sys.version_info < (3, 11))' \
  || { echo "error: python3 3.11 or later is required" >&2; exit 2; }

mkdir -p "$work"
work=$(cd "$work" && pwd)
if ((analyze_only)); then
  [[ -d "$work/profiles" ]] || { echo "error: $work/profiles is missing; run with --keep-profiles first" >&2; exit 2; }
  rm -rf "$work/export"
else
  rm -rf "$work/profiles" "$work/export" "$work/report" "$work/bins"
fi
mkdir -p "$work/profiles/build" "$work/export" "$work/report" "$work/bins"
log="$work/report/run.log"
: >"$log"

stamp() {
  printf '%s %s |%s\n' "$1" "$(date -Is)" "$(uptime)" | tee -a "$log" >&2
}

export CARGO_TARGET_DIR="$work/cargo-target"
export RUSTFLAGS="-C instrument-coverage -C llvm-args=-runtime-counter-relocation"
export CARGO_INCREMENTAL=0
export LLVM_PROFILE_FILE="$work/profiles/build/%p-%m.profraw"
export COVERAGE_WORKSPACE="$workspace" COVERAGE_LLVM_TOOLS="$LLVM_TOOLS" COVERAGE_JOBS="$jobs"
export PYTHONDONTWRITEBYTECODE=1
runner_variable="CARGO_TARGET_$(rustc -vV | sed -n 's/^host: //p' | tr 'a-z-' 'A-Z_')_RUNNER"

suites=(z3)
((portable)) && suites+=(portable)
status=0
cd "$workspace"
for suite in "${suites[@]}"; do
  ((analyze_only)) && break
  case "$suite" in
    z3) selection=(--workspace --no-default-features --features "k-rust/cli k-rust/z3-inference") ;;
    portable) selection=(-p k-rust -p k-rust-wasm --no-default-features) ;;
  esac
  stamp "$suite-build"
  # The listing builds every test binary; it also names each binary's package and kind.
  cargo nextest list "${selection[@]}" --locked --build-jobs "$jobs" --message-format json \
    >"$work/list-$suite.json" 2>"$work/report/build-$suite.log" \
    || { echo "error: the $suite build failed; see $work/report/build-$suite.log" >&2; exit 1; }
  # Tests run the krust that CARGO_BIN_EXE_krust names, which the next suite's build replaces.
  cp -p "$CARGO_TARGET_DIR/debug/krust" "$work/bins/krust-$suite"
  stamp "$suite-test"
  suite_status=0
  env "$runner_variable=$workspace/scripts/coverage/runner.sh" COVERAGE_PROFILE_DIR="$work/profiles/$suite" \
    cargo nextest run "${selection[@]}" --locked --no-fail-fast --test-threads "$jobs" "${run_arguments[@]}" \
    >"$work/report/nextest-$suite.log" 2>&1 || suite_status=$?
  grep -E '^ +Summary ' "$work/report/nextest-$suite.log" | tee -a "$log" >&2 || true
  if ((suite_status)); then
    echo "warning: the $suite suite exited with status $suite_status; see $work/report/nextest-$suite.log" | tee -a "$log" >&2
    status=1
  fi
done

# The algorithm cards and their sites, from the build of the z3 suite.
"$CARGO_TARGET_DIR/debug/algo-graph" graph -o "$work/export/graph.toml" >/dev/null 2>"$work/report/algo-graph.log" \
  || { echo "error: algo-graph graph failed; see $work/report/algo-graph.log" >&2; exit 1; }

for suite in "${suites[@]}"; do
  stamp "$suite-export"
  arguments=()
  [[ "$suite" == z3 ]] && ((per_test)) && arguments+=(--per-test)
  python3 "$workspace/scripts/coverage/collect.py" "$work" "$suite" "${arguments[@]}" 2>&1 | tee -a "$log" >&2
done
stamp report
python3 "$workspace/scripts/coverage/report.py" "$work" "$work/export/graph.toml" "${suites[@]}"
stamp finished

if ! grep -qx '## Problems (0)' "$work/report/summary.md"; then
  echo "warning: some profiles could not be attributed; see the Problems section of $work/report/summary.md" >&2
  status=1
fi
if ((!keep)); then
  rm -rf "$work/profiles" "$work/export"/*/
fi
exit "$status"
