#!/usr/bin/env bash

reference_job_memory_high_kib=${REFERENCE_DIFFERENTIAL_JOB_MEMORY_HIGH_KIB:-8388608}
reference_job_memory_max_kib=${REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB:-8388608}
reference_job_fallback_virtual_memory_kib=${REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB:-12582912}

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
  # the 12 GiB ceiling and kompile dies with "unable to create native thread".
  # Bound the reference JVM explicitly whenever the caller has not, so the
  # fallback stays runnable on any host without a user systemd manager.
  if [[ -z "${REFERENCE_DIFFERENTIAL_K_OPTS:-}" ]]; then
    export REFERENCE_DIFFERENTIAL_K_OPTS='-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m'
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
