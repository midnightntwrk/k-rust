#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-z3-acquisition.XXXXXX")
trap 'find "$work" -depth -delete' EXIT

fail() {
  echo "error: $*" >&2
  exit 1
}

tree_for() {
  local features=$1
  cargo tree \
    --manifest-path "$workspace/Cargo.toml" \
    -p k-rust \
    --no-default-features \
    --features "$features" \
    --locked \
    -e normal,build \
    --prefix depth \
    --format '{p}|{f}'
}

feature_closure_for() {
  local features=$1
  cargo tree \
    --manifest-path "$workspace/Cargo.toml" \
    -p k-rust \
    --no-default-features \
    --features "$features" \
    --locked \
    -e features \
    -i z3-sys \
    --prefix none \
    --format '{p}|{f}'
}

z3_sys_subtree() {
  awk '
    BEGIN { found = 0 }
    /^[0-9]+z3-sys / && !found {
      match($0, /^[0-9]+/)
      root_depth = substr($0, RSTART, RLENGTH) + 0
      found = 1
      print
      next
    }
    found {
      match($0, /^[0-9]+/)
      depth = substr($0, RSTART, RLENGTH) + 0
      if (depth <= root_depth) exit
      print
    }
    END { if (!found) exit 2 }
  '
}

check_system_mode() {
  local features=$1
  local closure tree subtree
  closure=$(feature_closure_for "$features")
  tree=$(tree_for "$features")
  subtree=$(z3_sys_subtree <<<"$tree") || fail "$features has no resolved z3-sys subtree"

  grep -Eq '^z3 v[^|]+\|$' <<<"$closure" || fail "$features does not select acquisition-free z3"
  grep -Eq '^z3-sys v[^|]+\|$' <<<"$closure" || fail "$features does not select acquisition-free z3-sys"
  if grep -Eq '(gh-release|bundled|vendored|vcpkg)' <<<"$closure"; then
    fail "$features enables a Z3 acquisition feature"
  fi
  if grep -Eq '^[0-9]+(reqwest|zip|z3-src|vcpkg) v' <<<"$subtree"; then
    fail "$features includes an acquisition dependency below z3-sys"
  fi
}

check_default_mode() {
  local closure tree subtree
  closure=$(cargo tree \
    --manifest-path "$workspace/Cargo.toml" \
    -p k-rust \
    --locked \
    -e features \
    -i z3-sys \
    --prefix none \
    --format '{p}|{f}')
  tree=$(cargo tree \
    --manifest-path "$workspace/Cargo.toml" \
    -p k-rust \
    --locked \
    -e normal,build \
    --prefix depth \
    --format '{p}|{f}')
  subtree=$(z3_sys_subtree <<<"$tree") || fail "the default graph has no resolved z3-sys subtree"

  grep -Eq '^z3 v[^|]+\|gh-release$' <<<"$closure" || fail "the default graph does not select z3/gh-release"
  grep -Eq '^z3-sys v[^|]+\|gh-release$' <<<"$closure" || fail "the default graph does not select z3-sys/gh-release"
  grep -Eq '^[0-9]+reqwest v' <<<"$subtree" || fail "the default z3-sys graph has no GitHub download client"
  grep -Eq '^[0-9]+zip v' <<<"$subtree" || fail "the default z3-sys graph has no release archive reader"
}

echo "[graph] checking system-linked library features"
check_system_mode z3-inference

echo "[graph] checking system-linked CLI features"
check_system_mode cli

echo "[graph] checking the default GitHub-release positive control"
check_default_mode

echo "[runtime] exercising Z3 inference against the system library"
CARGO_TARGET_DIR="$work/target" cargo test \
  --manifest-path "$workspace/Cargo.toml" \
  -p k-rust \
  --test inner_rules \
  --no-default-features \
  --features z3-inference \
  --locked \
  z3_prunes_ill_typed_ambiguity_branches

echo "[runtime] exercising the system-linked CLI"
inference=$(CARGO_TARGET_DIR="$work/target" cargo run \
  --quiet \
  --manifest-path "$workspace/Cargo.toml" \
  -p k-rust \
  --bin krust \
  --no-default-features \
  --features cli \
  --locked \
  -- kast "$workspace/examples/z3-inference.k" \
  --module Z3-INFERENCE \
  --sort Box \
  --expression 'box(same(1))' \
  --no-prelude)
grep -Fq 'box(same(#token("1","Int")))' <<<"$inference" || fail "the system-linked CLI did not perform Z3 inference"

echo "Z3 acquisition graphs and system-linked runtime passed"
