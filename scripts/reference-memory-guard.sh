#!/usr/bin/env bash

rust_memory_high_kib=${RUST_DIFFERENTIAL_MEMORY_HIGH_KIB:-6291456}
rust_memory_max_kib=${RUST_DIFFERENTIAL_MEMORY_MAX_KIB:-8388608}
rust_fallback_virtual_memory_kib=${RUST_DIFFERENTIAL_FALLBACK_VIRTUAL_MEMORY_KIB:-12582912}

reference_require_positive_kib() {
  local name=$1
  local value=$2
  if [[ ! "$value" =~ ^[1-9][0-9]*$ ]]; then
    echo "error: $name must be a positive KiB integer" >&2
    return 2
  fi
}

reference_run_rust_frontend() {
  local -a scope_properties
  reference_require_positive_kib \
    RUST_DIFFERENTIAL_MEMORY_HIGH_KIB "$rust_memory_high_kib" || return
  reference_require_positive_kib \
    RUST_DIFFERENTIAL_MEMORY_MAX_KIB "$rust_memory_max_kib" || return
  reference_require_positive_kib \
    RUST_DIFFERENTIAL_FALLBACK_VIRTUAL_MEMORY_KIB \
    "$rust_fallback_virtual_memory_kib" || return
  if ((rust_memory_high_kib > rust_memory_max_kib)); then
    echo "error: RUST_DIFFERENTIAL_MEMORY_HIGH_KIB must not exceed RUST_DIFFERENTIAL_MEMORY_MAX_KIB" >&2
    return 2
  fi

  # Probe separately so a nonzero command status is never mistaken for an
  # unavailable user manager and executed a second time through the fallback.
  scope_properties=(
    -p "MemoryHigh=${rust_memory_high_kib}K"
    -p "MemoryMax=${rust_memory_max_kib}K"
    -p MemorySwapMax=0
  )
  if command -v systemd-run >/dev/null 2>&1 && \
    systemd-run --user --scope --quiet \
      "${scope_properties[@]}" -- true >/dev/null 2>&1; then
    systemd-run --user --scope --quiet \
      "${scope_properties[@]}" -- "$@"
    return
  fi

  echo "warning: user systemd scopes unavailable; applying the $rust_fallback_virtual_memory_kib KiB virtual-memory fallback to k-rust" >&2
  (
    ulimit -v "$rust_fallback_virtual_memory_kib"
    exec "$@"
  )
}
