#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-pins.sh"
imp_checkout=${IMP_SEMANTICS_CHECKOUT:-"$workspace/imp-semantics"}
kompile=${K_KOMPILE:-}
krun=${K_KRUN:-}
kore_parser=${K_KORE_PARSER:-}
kore_rpc=${K_KORE_RPC:-}
rpc_client=${K_KORE_RPC_CLIENT:-}
reference_port=${REFERENCE_RPC_PORT:-31347}
rust_port=${RUST_RPC_PORT:-31348}
reference_memory_kib=${REFERENCE_EXECUTION_MEMORY_KIB:-12582912}
rust_memory_kib=${RUST_DIFFERENTIAL_MEMORY_KIB:-6291456}
reference_retries=${REFERENCE_EXECUTION_RETRIES:-3}
reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-'-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m -Dscala.concurrent.context.numThreads=4 -Dscala.concurrent.context.maxThreads=4'}
manifest_json=$(
  WORKSPACE="$workspace" IMP_SEMANTICS_CHECKOUT="$imp_checkout" \
    "$workspace/scripts/reference-manifest.py"
)
rpc=$(jq -c '.rpc[] | select(.name == "imp")' <<<"$manifest_json")

if [[ -z "$kompile" ]]; then
  kompile=$(command -v kompile || true)
fi
if [[ -z "$kompile" || ! -x "$kompile" ]]; then
  echo "error: set K_KOMPILE to the pinned reference kompile executable" >&2
  exit 2
fi
reference_bin=$(dirname "$kompile")
krun=${krun:-"$reference_bin/krun"}
kore_parser=${kore_parser:-"$reference_bin/kore-parser"}
kore_rpc=${kore_rpc:-"$reference_bin/kore-rpc"}
rpc_client=${rpc_client:-"$reference_bin/kore-rpc-client"}
for tool in "$krun" "$kore_parser" "$kore_rpc" "$rpc_client"; do
  if [[ ! -x "$tool" ]]; then
    echo "error: missing matching pinned reference executable: $tool" >&2
    exit 2
  fi
done

semantics=$(jq -r '.source' <<<"$rpc")
program=$(jq -r '.program' <<<"$rpc")
main_module=$(jq -r '.["main-module"]' <<<"$rpc")
syntax_module=$(jq -r '.["syntax-module"]' <<<"$rpc")
mapfile -t configuration_args < <(jq -r '.configuration[] | "-c" + .' <<<"$rpc")
if [[ ! -f "$semantics" || ! -f "$program" ]]; then
  echo "error: set IMP_SEMANTICS_CHECKOUT to the pinned IMP checkout" >&2
  exit 2
fi
reference_require_k_version "$kompile"
reference_require_git_pin IMP "$imp_checkout" "$IMP_REFERENCE_REVISION"

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-rpc-differential.XXXXXX")
server_pid=
cleanup() {
  if [[ -n "$server_pid" ]]; then
    kill "$server_pid" 2>/dev/null || true
    wait "$server_pid" 2>/dev/null || true
  fi
  rm -rf "$work"
}
trap cleanup EXIT

stop_server() {
  if [[ -n "$server_pid" ]]; then
    kill "$server_pid" 2>/dev/null || true
    wait "$server_pid" 2>/dev/null || true
    server_pid=
  fi
}

wait_for_server() {
  local port=$1
  local attempt
  for ((attempt = 1; attempt <= 100; attempt++)); do
    if (exec 3<>"/dev/tcp/127.0.0.1/$port") 2>/dev/null; then
      return 0
    fi
    if ! kill -0 "$server_pid" 2>/dev/null; then
      echo "error: RPC server exited before listening on port $port" >&2
      cat "$work/server.log" >&2
      return 1
    fi
    sleep 0.1
  done
  echo "error: RPC server did not listen on port $port" >&2
  cat "$work/server.log" >&2
  return 1
}

run_reference_krun() {
  local output=$1
  shift
  local attempt
  for ((attempt = 1; attempt <= reference_retries; attempt++)); do
    if (
      ulimit -v "$reference_memory_kib"
      export GHCRTS=${GHCRTS:--N1}
      "$krun" "$@" >"$output"
    ); then
      return 0
    fi
    rm -f "$output"
    if ((attempt < reference_retries)); then
      echo "reference krun preprocessing failed; retrying ($attempt/$reference_retries)" >&2
    fi
  done
  return 1
}

send_raw() {
  local port=$1
  local request=$2
  local output=$3
  local response
  exec {rpc_fd}<>"/dev/tcp/127.0.0.1/$port"
  printf '%s\n' "$request" >&"$rpc_fd"
  IFS= read -r response <&"$rpc_fd"
  exec {rpc_fd}>&-
  printf '%s\n' "$response" >"$output"
}

collect_responses() {
  local port=$1
  local prefix=$2
  export GHCRTS=
  "$rpc_client" --port "$port" execute "$work/state.json" \
    -O max-depth=1 -o "$work/$prefix-execute.json"
  "$rpc_client" --port "$port" simplify "$work/bool.json" \
    -o "$work/$prefix-simplify.json"
  "$rpc_client" --port "$port" send "$work/implies-request.json" \
    -o "$work/$prefix-implies.json"
  "$rpc_client" --port "$port" get-model "$work/model.json" \
    -o "$work/$prefix-model.json"
  "$rpc_client" --port "$port" send "$work/add-module-request.json" \
    -o "$work/$prefix-add-module.json"
  send_raw "$port" \
    '{"jsonrpc":"2.0","id":"unknown-1","method":"unknown"}' \
    "$work/$prefix-error.json"
}

echo "[imp:rpc] compiling the reference Haskell definition"
(
  ulimit -v "$reference_memory_kib"
  export GHCRTS=${GHCRTS:--N1}
  export K_OPTS="$reference_k_opts"
  "$kompile" "$semantics" \
    --backend haskell \
    --main-module "$main_module" \
    --syntax-module "$syntax_module" \
    --output-definition "$work/kompiled" \
    --warnings none
)

echo "[imp:rpc] generating a depth-zero reference configuration"
run_reference_krun "$work/state.kore" \
  "$program" \
  --definition "$work/kompiled" \
  "${configuration_args[@]}" \
  --depth 0 \
  --smt none \
  --output kore

echo "[imp:rpc] converting the configuration to KORE JSON"
(
  ulimit -v "$rust_memory_kib"
  export GHCRTS=
  "$kore_parser" "$work/kompiled/definition.kore" \
    --pattern "$work/state.kore" \
    --module "$main_module" \
    --print-pattern-json \
    --no-print-definition >"$work/state.json"
)

jq -n '{
  format: "KORE",
  version: 1,
  term: {
    tag: "DV",
    sort: {tag: "SortApp", name: "SortBool", args: []},
    value: "true"
  }
}' >"$work/bool.json"
jq '{
  jsonrpc: "2.0",
  id: 1,
  method: "implies",
  params: {antecedent: ., consequent: ., "assume-defined": true}
}' "$work/state.json" >"$work/implies-request.json"
jq '{
  format: "KORE",
  version: 1,
  term: {
    tag: "Equals",
    argSort: {tag: "SortApp", name: "SortGeneratedTopCell", args: []},
    sort: {tag: "SortApp", name: "SortGeneratedTopCell", args: []},
    first: .term,
    second: .term
  }
}' "$work/state.json" >"$work/model.json"
jq -n '{
  jsonrpc: "2.0",
  id: 1,
  method: "add-module",
  params: {module: "module RPC-EXTRA\nendmodule []", "name-as-id": true}
}' >"$work/add-module-request.json"

echo "[imp:rpc] collecting pinned reference responses"
(
  ulimit -v "$reference_memory_kib"
  export GHCRTS=${GHCRTS:--N1}
  exec "$kore_rpc" "$work/kompiled/definition.kore" \
    --module "$main_module" \
    --smt none \
    --server-port "$reference_port" \
    --no-bug-report
) >"$work/server.log" 2>&1 &
server_pid=$!
wait_for_server "$reference_port"
collect_responses "$reference_port" reference
stop_server

echo "[imp:rpc] building the Rust RPC server"
(
  ulimit -v "$rust_memory_kib"
  export CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2}
  cargo build --quiet --release --manifest-path "$workspace/Cargo.toml" \
    -p k-rust --bin krust
)

echo "[imp:rpc] collecting Rust responses"
(
  ulimit -v "$rust_memory_kib"
  exec "$workspace/target/release/krust" kore-rpc "$work/kompiled/definition.kore" \
    --module IMP \
    --server-port "$rust_port"
) >"$work/server.log" 2>&1 &
server_pid=$!
wait_for_server "$rust_port"
collect_responses "$rust_port" rust
stop_server

mapfile -t responses < <(jq -r '.responses[]' <<<"$rpc")
for response in "${responses[@]}"; do
  echo "[imp:rpc:$response] comparing JSON response"
  if ! diff -u \
    <(jq -S . "$work/reference-$response.json") \
    <(jq -S . "$work/rust-$response.json"); then
    echo "error: RPC response differs for $response" >&2
    exit 1
  fi
done

echo "reference IMP JSON-RPC differential corpus passed"
