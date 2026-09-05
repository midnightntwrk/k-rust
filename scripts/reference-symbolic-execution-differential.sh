#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-memory-guard.sh"
reference_enter_whole_job "$@"
source "$workspace/scripts/reference-pins.sh"
k_checkout=${K_CHECKOUT:-"$workspace/k"}
kompile=${K_KOMPILE:-}
kore_exec=${K_KORE_EXEC:-}
kore_parser=${K_KORE_PARSER:-}
reference_memory_kib=${REFERENCE_EXECUTION_MEMORY_KIB:-8388608}
rust_memory_kib=${RUST_DIFFERENTIAL_MEMORY_KIB:-6291456}
cargo_target_dir=${CARGO_TARGET_DIR:-"$workspace/target"}
reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-$reference_default_k_opts}
manifest_json=$(
  WORKSPACE="$workspace" K_CHECKOUT="$k_checkout" \
    "$workspace/scripts/reference-manifest.py"
)

mapfile -t available < <(
  jq -r '.symbolic[] |
    select((.requires | index("semantics-support")) == null) | .name' <<<"$manifest_json"
)
selected=("${available[@]}")
if (($#)); then
  selected=("$@")
fi
runnable=()
for name in "${selected[@]}"; do
  if ! printf '%s\n' "${available[@]}" | grep -Fxq "$name"; then
    echo "error: unknown symbolic execution case: $name" >&2
    echo "available cases: ${available[*]}" >&2
    exit 2
  fi
  suite=$(jq -c --arg name "$name" '.symbolic[] | select(.name == $name)' <<<"$manifest_json")
  blocking_tickets=$(jq -r '[.requires[] | select(startswith("ticket:")) | ltrimstr("ticket:")] | join(", ")' <<<"$suite")
  if [[ -n "$blocking_tickets" && "${REFERENCE_DIFFERENTIAL_PENDING:-0}" != 1 ]]; then
    echo "[$name] pending: blocked by $blocking_tickets"
  else
    runnable+=("$name")
  fi
done
if ((${#runnable[@]} == 0)); then
  echo "reference symbolic execution differential corpus passed"
  exit 0
fi

if [[ -z "$kompile" ]]; then
  kompile=$(command -v kompile || true)
fi
if [[ -z "$kompile" || ! -x "$kompile" ]]; then
  echo "error: set K_KOMPILE to the pinned reference kompile executable" >&2
  exit 2
fi
reference_bin=$(dirname "$kompile")
kore_exec=${kore_exec:-"$reference_bin/kore-exec"}
kore_parser=${kore_parser:-"$reference_bin/kore-parser"}
for tool in "$kore_exec" "$kore_parser"; do
  if [[ ! -x "$tool" ]]; then
    echo "error: missing matching pinned reference executable: $tool" >&2
    exit 2
  fi
done
if [[ ! -d "$k_checkout/k-distribution/include/kframework/builtin" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi
reference_require_k_version "$kompile"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-symbolic.XXXXXX")
if [[ "${REFERENCE_DIFFERENTIAL_KEEP_WORK:-0}" == 1 ]]; then
  trap 'echo "symbolic differential artifacts retained at: $work"' EXIT
else
  trap 'find "$work" -depth -delete' EXIT
fi

run_reference_tool() (
  ulimit -v "$reference_memory_kib"
  export K_OPTS="$reference_k_opts"
  "$@"
)

run_reference_parser() (
  export GHCRTS=
  run_reference_tool "$@"
)

run_reference_backend() (
  export GHCRTS=${GHCRTS:--N1}
  run_reference_tool "$@"
)

echo "[symbolic] building the Rust execution frontend"
(
  ulimit -v "$rust_memory_kib"
  export CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2}
  cargo build --quiet --release --manifest-path "$workspace/Cargo.toml" \
    -p k-rust --bin krust
)
krust="$cargo_target_dir/release/krust"

for name in "${runnable[@]}"; do
  suite=$(jq -c --arg name "$name" '.symbolic[] | select(.name == $name)' <<<"$manifest_json")
  source=$(jq -r '.source' <<<"$suite")
  main_module=$(jq -r '.["main-module"]' <<<"$suite")
  syntax_module=$(jq -r '.["syntax-module"] // empty' <<<"$suite")
  definition_mode=$(jq -r '.definition' <<<"$suite")
  include=$(jq -r '.include // empty' <<<"$suite")
  selector=$(jq -r '.["markdown-selector"] // empty' <<<"$suite")
  mapfile -t hook_namespaces < <(jq -r '(.["hook-namespaces"] // [])[]' <<<"$suite")
  if [[ ! -f "$source" ]]; then
    echo "error: missing $name symbolic semantics source: $source" >&2
    exit 2
  fi
  include_args=()
  selector_args=()
  syntax_args=()
  reference_hook_args=()
  rust_hook_args=()
  if [[ -n "$include" ]]; then
    include_args=(-I "$include")
  fi
  if [[ -n "$selector" ]]; then
    selector_args=(--md-selector "$selector")
  elif [[ "$source" == *.md ]]; then
    selector_args=(--md-selector 'k & ! concrete')
  fi
  if [[ -n "$syntax_module" ]]; then
    syntax_args=(--syntax-module "$syntax_module")
  fi
  if ((${#hook_namespaces[@]})); then
    reference_hook_args=(--hook-namespaces "${hook_namespaces[*]}")
    rust_hook_args=(--hook-namespaces "$(IFS=,; echo "${hook_namespaces[*]}")")
  fi

  reference_definition="$work/$name/reference-kompiled"
  echo "[$name] compiling and verifying the reference Haskell definition"
  run_reference_backend "$kompile" "$source" \
    --backend haskell \
    --main-module "$main_module" \
    --output-definition "$reference_definition" \
    "${include_args[@]}" \
    "${selector_args[@]}" \
    "${syntax_args[@]}" \
    "${reference_hook_args[@]}" \
    --warnings none
  run_reference_parser "$kore_parser" "$reference_definition/definition.kore" \
    >"$work/$name/verify-reference.log" 2>&1

  rust_definition="$work/$name/rust-kompiled"
  if [[ "$definition_mode" == rust || "$definition_mode" == both ]]; then
    echo "[$name] compiling and verifying the k-rust definition"
    "$krust" kcompile "$source" \
      --backend rust \
      --main-module "$main_module" \
      --output-directory "$rust_definition" \
      "${include_args[@]}" \
      "${selector_args[@]}" \
      "${syntax_args[@]}" \
      "${rust_hook_args[@]}" \
      --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin"
    run_reference_parser "$kore_parser" "$rust_definition/definition.kore" \
      >"$work/$name/verify-rust.log" 2>&1
  fi

  definition_labels=()
  definition_paths=()
  case "$definition_mode" in
    reference)
      definition_labels=(reference)
      definition_paths=("$reference_definition/definition.kore")
      ;;
    rust)
      definition_labels=(rust)
      definition_paths=("$rust_definition/definition.kore")
      ;;
    both)
      definition_labels=(reference rust)
      definition_paths=(
        "$reference_definition/definition.kore"
        "$rust_definition/definition.kore"
      )
      ;;
    *)
      echo "error: invalid definition mode for $name: $definition_mode" >&2
      exit 2
      ;;
  esac

  mapfile -t patterns < <(
    jq -r '.pattern[] | [
      .name,
      .pattern,
      .mode,
      (.depth // ""),
      (.bound // ""),
      (.["search-pattern"] // .pattern),
      (.["oracle-exclusion"] // "")
    ] | join("\u001f")' <<<"$suite"
  )
  for pattern_row in "${patterns[@]}"; do
    IFS=$'\x1f' read -r pattern_name pattern mode depth bound search_pattern oracle_exclusion <<<"$pattern_row"
    if [[ ! -f "$pattern" || ! -f "$search_pattern" ]]; then
      echo "error: missing symbolic pattern for $name:$pattern_name" >&2
      exit 2
    fi
    depth_args=()
    if [[ -n "$depth" ]]; then
      depth_args=(--depth "$depth")
    fi
    reference_bound_args=()
    rust_bound_args=()
    if [[ -n "$bound" ]]; then
      reference_bound_args=(--bound "$bound")
      rust_bound_args=(--search-bound "$bound")
    fi
    case "$mode" in
      exec)
        reference_search_args=()
        rust_search_args=()
        ;;
      search-final)
        reference_search_args=(--search "$search_pattern" --searchType FINAL)
        rust_search_args=(--search-final --search-pattern "$search_pattern")
        ;;
      search-all)
        reference_search_args=(--search "$search_pattern" --searchType STAR)
        rust_search_args=(--search-all --search-pattern "$search_pattern")
        ;;
      search-one-step)
        reference_search_args=(--search "$search_pattern" --searchType ONE)
        rust_search_args=(--search-one-step --search-pattern "$search_pattern")
        ;;
      search-one-or-more-steps)
        reference_search_args=(--search "$search_pattern" --searchType PLUS)
        rust_search_args=(--search-one-or-more-steps --search-pattern "$search_pattern")
        ;;
      *)
        echo "error: invalid symbolic mode for $name:$pattern_name: $mode" >&2
        exit 2
        ;;
    esac
    if [[ "$oracle_exclusion" == gotstuck && ( "$mode" != exec || -z "$depth" ) ]]; then
      echo "error: gotstuck requires a depth-bounded exec pattern" >&2
      exit 2
    fi

    for index in "${!definition_paths[@]}"; do
      definition_label=${definition_labels[index]}
      definition=${definition_paths[index]}
      stem="$work/$name/$pattern_name-$definition_label"
      echo "[$name:$pattern_name:$definition_label] verifying the input pattern"
      run_reference_parser "$kore_parser" "$definition" \
        --pattern "$pattern" \
        --module "$main_module" \
        --no-print-definition >"$stem.verify.log" 2>&1

      echo "[$name:$pattern_name:$definition_label] executing with kore-exec"
      run_reference_backend "$kore_exec" "$definition" \
        --module "$main_module" \
        --pattern "$pattern" \
        "${depth_args[@]}" \
        "${reference_search_args[@]}" \
        "${reference_bound_args[@]}" \
        --output "$stem.reference.kore"

      stop_args=()
      stop_leaves=
      if [[ "$oracle_exclusion" == gotstuck ]]; then
        stop_leaves="$stem.stop-leaves.kore"
        stop_args=(--stop-leaves "$stop_leaves")
      fi
      echo "[$name:$pattern_name:$definition_label] executing with k-rust kore-exec"
      "$krust" kore-exec "$definition" \
        --module "$main_module" \
        --pattern "$pattern" \
        "${depth_args[@]}" \
        "${rust_search_args[@]}" \
        "${rust_bound_args[@]}" \
        "${stop_args[@]}" \
        --output "$stem.rust.kore"

      comparison_environment=(
        K_REFERENCE_EXECUTION="$stem.reference.kore"
        K_RUST_EXECUTION="$stem.rust.kore"
        K_DIFFERENTIAL_DEFINITION="$definition"
        K_DIFFERENTIAL_MODULE="$main_module"
        K_DIFFERENTIAL_INITIAL_PATTERN="$pattern"
        K_RUST_KRUST="$krust"
      )
      if [[ -n "$oracle_exclusion" ]]; then
        comparison_environment+=(
          K_DIFFERENTIAL_ORACLE_EXCLUSION="$oracle_exclusion"
          K_DIFFERENTIAL_STOP_LEAVES="$stop_leaves"
        )
      fi
      env "${comparison_environment[@]}" \
        cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
          -p k-rust --test reference_differential -- --ignored --exact \
          executed_kore_matches_the_reference_backend
    done
  done
done

echo "reference symbolic execution differential corpus passed"
