#!/usr/bin/env bash

reference_default_k_opts='-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m -Dscala.concurrent.context.numThreads=2 -Dscala.concurrent.context.maxThreads=2'
reference_job_memory_high_kib=${REFERENCE_DIFFERENTIAL_JOB_MEMORY_HIGH_KIB:-16777216}
reference_job_memory_max_kib=${REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB:-16777216}
reference_job_fallback_virtual_memory_kib=${REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB:-25165824}

# The cargo arguments of every build or run of `krust` in a conformance or reference
# gate. The kompile invariant checkers are compiled only under debug assertions or the
# `kompile-invariant-checks` feature, and the gates build release binaries, so without
# the feature the checkers never see the corpus these gates compile. The checked
# binary goes to its own target directory: scripts/benchmark.sh measures
# target/release/krust and scripts/profile.sh target/profiling/krust, and a gate must
# never replace either with a binary that runs the checkers. KRUST_GATE_TARGET_DIR
# moves that directory; KRUST_GATE_INVARIANT_CHECKS=0 builds without the feature.
krust_gate_target_dir=${KRUST_GATE_TARGET_DIR:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/target/gates"}
if [[ "$krust_gate_target_dir" != /* ]]; then
  krust_gate_target_dir=$PWD/$krust_gate_target_dir
fi
krust_gate_cargo_args=(--target-dir "$krust_gate_target_dir")
case ${KRUST_GATE_INVARIANT_CHECKS:-1} in
  1)
    krust_gate_cargo_args+=(--features kompile-invariant-checks)
    krust_gate_build_description="with kompile-invariant-checks"
    ;;
  0)
    krust_gate_build_description="without kompile-invariant-checks (KRUST_GATE_INVARIANT_CHECKS=0)"
    ;;
  *)
    echo "error: KRUST_GATE_INVARIANT_CHECKS must be 0 or 1" >&2
    return 2
    ;;
esac
# The release binary that `cargo build --release "${krust_gate_cargo_args[@]}"` writes.
krust_gate_binary="$krust_gate_target_dir/release/krust"

reference_announce_krust_gate_build() {
  echo "[gate] krust is built $krust_gate_build_description into $krust_gate_target_dir"
}

# reference_build_comparator WORKSPACE [CARGO ARGUMENT...]
#   Builds the reference_differential comparator test binary once and prints its path, so a gate
#   runs it directly instead of paying a cargo freshness check per comparison. Without further
#   arguments it is the binary `cargo test -p k-rust --test reference_differential` runs; run it
#   from crates/k-rust, the directory cargo runs it in.
reference_build_comparator() {
  local workspace=$1
  local executable
  shift
  executable=$(
    cargo test --quiet --no-run --message-format=json-render-diagnostics "$@" \
      --manifest-path "$workspace/Cargo.toml" -p k-rust --test reference_differential |
      jq -r 'select(.reason == "compiler-artifact" and .target.name == "reference_differential"
        and .profile.test) | .executable // empty' | tail -n 1
  ) || return
  if [[ ! -x "$executable" ]]; then
    echo "error: cargo reported no reference_differential test executable" >&2
    return 2
  fi
  printf '%s\n' "$executable"
}

reference_require_positive_kib() {
  local name=$1
  local value=$2
  if [[ ! "$value" =~ ^[1-9][0-9]*$ ]]; then
    echo "error: $name must be a positive KiB integer" >&2
    return 2
  fi
}

reference_enter_whole_job() {
  local script=${BASH_SOURCE[1]:-}
  local guard_kind=${REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND:-}
  local -a scope_properties

  reference_require_positive_kib \
    REFERENCE_DIFFERENTIAL_JOB_MEMORY_HIGH_KIB \
    "$reference_job_memory_high_kib" || return
  reference_require_positive_kib \
    REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB \
    "$reference_job_memory_max_kib" || return
  reference_require_positive_kib \
    REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB \
    "$reference_job_fallback_virtual_memory_kib" || return
  if ((reference_job_memory_high_kib > reference_job_memory_max_kib)); then
    echo "error: REFERENCE_DIFFERENTIAL_JOB_MEMORY_HIGH_KIB must not exceed REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB" >&2
    return 2
  fi

  case "$guard_kind" in
    systemd-scope | rlimit-as)
      return 0
      ;;
    "")
      ;;
    *)
      echo "error: invalid internal REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND: $guard_kind" >&2
      return 2
      ;;
  esac

  if [[ -z "$script" ]]; then
    echo "error: reference_enter_whole_job must be called from a differential script" >&2
    return 2
  fi
  if [[ "$script" != /* ]]; then
    script=$(cd "$(dirname "$script")" && pwd)/$(basename "$script")
  fi

  # Probe separately so a nonzero command status is never mistaken for an
  # unavailable user manager and executed a second time through the fallback.
  scope_properties=(
    -p "MemoryHigh=${reference_job_memory_high_kib}K"
    -p "MemoryMax=${reference_job_memory_max_kib}K"
    -p MemorySwapMax=0
  )
  if command -v systemd-run >/dev/null 2>&1 && \
    systemd-run --user --scope --quiet \
      "${scope_properties[@]}" -- true >/dev/null 2>&1; then
    export REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND=systemd-scope
    exec systemd-run --user --scope --quiet \
      "${scope_properties[@]}" -- "$BASH" "$script" "$@"
  fi

  echo "warning: user systemd scopes unavailable; applying the $reference_job_fallback_virtual_memory_kib KiB whole-job virtual-address fallback (RLIMIT_AS), not a resident-memory limit" >&2
  export REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND=rlimit-as
  # RLIMIT_AS bounds virtual address space, and a JVM left to its default
  # ergonomics reserves heap, GC worker stacks, and code cache proportional to
  # machine RAM and core count; on a 16-core host that reservation alone exceeds
  # the 24 GiB ceiling and kompile dies with "unable to create native thread".
  # Bound the reference JVM explicitly whenever the caller has not, so the
  # fallback stays runnable on any host without a user systemd manager.
  if [[ -z "${REFERENCE_DIFFERENTIAL_K_OPTS:-}" ]]; then
    export REFERENCE_DIFFERENTIAL_K_OPTS="$reference_default_k_opts"
    echo "warning: bounding the reference JVM with REFERENCE_DIFFERENTIAL_K_OPTS=$REFERENCE_DIFFERENTIAL_K_OPTS under the virtual-address fallback" >&2
  fi
  if ! ulimit -v "$reference_job_fallback_virtual_memory_kib"; then
    echo "error: could not apply the whole-job virtual-address fallback" >&2
    return 2
  fi
  exec "$BASH" "$script" "$@"
}

reference_run_rust_frontend() {
  case ${REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND:-} in
    systemd-scope | rlimit-as)
      "$@"
      ;;
    *)
      echo "error: reference_run_rust_frontend requires the whole-job memory guard" >&2
      return 2
      ;;
  esac
}
