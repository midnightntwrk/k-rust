#!/usr/bin/env bash
# Cargo target runner for scripts/coverage.sh: give each test process its own profile directory.
#
# nextest runs every test as `BINARY --exact NAME ...`. The test, and every process it starts
# (krust children, a rerun of its own binary), inherit LLVM_PROFILE_FILE and write their
# profiles to COVERAGE_PROFILE_DIR/BINARY/NAME. Any other invocation, such as nextest's
# `--list`, writes below COVERAGE_PROFILE_DIR/_other. `%p` keeps processes apart; `%c` selects
# continuous mode, in which counters are written while the process runs, so a process that is
# killed keeps its profile.
set -euo pipefail
binary=$1
shift
name=""
previous=""
for argument in "$@"; do
  [[ "$previous" == "--exact" ]] && name=$argument
  previous=$argument
done
if [[ -n "$name" ]]; then
  directory="$COVERAGE_PROFILE_DIR/$(basename "$binary")/${name//\//_}"
else
  directory="$COVERAGE_PROFILE_DIR/_other"
fi
mkdir -p "$directory"
export LLVM_PROFILE_FILE="$directory/p-%p%c.profraw"
exec "$binary" "$@"
