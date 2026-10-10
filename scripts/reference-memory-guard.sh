#!/usr/bin/env bash

reference_default_k_opts='-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m -Dscala.concurrent.context.numThreads=2 -Dscala.concurrent.context.maxThreads=2'
reference_job_memory_high_kib=${REFERENCE_DIFFERENTIAL_JOB_MEMORY_HIGH_KIB:-16777216}
reference_job_memory_max_kib=${REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB:-16777216}
reference_job_fallback_virtual_memory_kib=${REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB:-25165824}
# The guard this shell entered (reference_enter_whole_job); never taken from the environment.
reference_job_guard_kind=

# The cargo arguments of every build or run of `krust` in a conformance or reference
# gate. The kompile invariant checkers are compiled only under debug assertions or the
# `kompile-invariant-checks` feature, and the gates build release binaries, so without
# the feature the checkers never see the corpus these gates compile. The checked
# binary goes to its own target directory: scripts/benchmark.sh measures
# target/release/krust and scripts/profile.sh target/profiling/krust, and a gate must
# never replace either with a binary that runs the checkers. KRUST_GATE_TARGET_DIR
# moves that directory; KRUST_GATE_INVARIANT_CHECKS=0 builds without the feature.
#
# KRUST_GATE_Z3 selects how the Z3 library is acquired, for krust and for the comparator.
# `gh-release` (the default) builds Cargo's default features, whose z3-sys build script
# downloads the Z3 release archive. `system` builds `--no-default-features --features cli`:
# `cli` already enables `z3-inference`, so the code and the features are the same, and only
# the download is left out; z3-sys then links the Z3 the build environment provides
# (pkg-config, or its Z3_* variables, as `with-z3-static-4.16.0` sets them).
krust_gate_target_dir=${KRUST_GATE_TARGET_DIR:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/target/gates"}
if [[ "$krust_gate_target_dir" != /* ]]; then
  krust_gate_target_dir=$PWD/$krust_gate_target_dir
fi
case ${KRUST_GATE_Z3:-gh-release} in
  gh-release)
    krust_gate_z3_args=()
    ;;
  system)
    krust_gate_z3_args=(--no-default-features --features cli)
    ;;
  *)
    echo "error: KRUST_GATE_Z3 must be gh-release or system" >&2
    return 2
    ;;
esac
krust_gate_cargo_args=(--target-dir "$krust_gate_target_dir" "${krust_gate_z3_args[@]}")
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
# shellcheck disable=SC2034  # the gate scripts that source this file execute it
krust_gate_binary="$krust_gate_target_dir/release/krust"

reference_announce_krust_gate_build() {
  echo "[gate] krust is built $krust_gate_build_description into $krust_gate_target_dir"
}

# reference_build_comparator WORKSPACE [CARGO ARGUMENT...]
#   Builds the reference_differential comparator test binary once and prints its path, so a gate
#   runs it directly instead of paying a cargo freshness check per comparison. With only
#   "${krust_gate_z3_args[@]}" it is the binary `cargo test -p k-rust --test reference_differential`
#   runs; a caller that shares the gate krust's build passes "${krust_gate_cargo_args[@]}", which
#   holds the same Z3 selection. Run it from crates/k-rust, the directory cargo runs it in.
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

# reference_close_inherited_descriptors
#   Closes every descriptor above 2 that a process this shell starts would inherit, that is every
#   one without close-on-exec. Bash opens its own descriptors (the script it reads) close-on-exec,
#   so these are the caller's: a pipe or a listening socket the caller left open would otherwise
#   reach every reference process, and a server holding the caller's listener can be found on the
#   caller's port instead of its own.
reference_close_inherited_descriptors() {
  local entry descriptor key value flags
  local -a inherited=()
  for entry in "/proc/$$/fd/"*; do
    descriptor=${entry##*/}
    if [[ ! "$descriptor" =~ ^[0-9]+$ ]] || ((descriptor <= 2)); then
      continue
    fi
    flags=
    { while read -r key value; do
        if [[ "$key" == flags: ]]; then
          flags=$value
        fi
      done <"/proc/$$/fdinfo/$descriptor"; } 2>/dev/null || continue
    # O_CLOEXEC is octal 02000000 in the flags fdinfo reports.
    if [[ "$flags" =~ ^[0-7]+$ ]] && (((8#$flags & 8#2000000) == 0)); then
      inherited+=("$descriptor")
    fi
  done
  for descriptor in "${inherited[@]}"; do
    eval "exec $descriptor>&-"
  done
}

# reference_scope_placement
#   Where the job's scope goes, and what it must not exceed. The user manager creates a scope in
#   one of its slices, and a process moved there leaves every cgroup of its path that is not that
#   slice or an ancestor of it, together with that cgroup's limits. So the scope goes in the
#   deepest slice of the caller's own path, which keeps every cgroup above it, and its memory
#   limits must be no larger than the memory.max and memory.high of each cgroup it leaves. Sets
#   reference_scope_slice (empty: the caller is in no slice of the user manager, which then picks
#   its default slice) and reference_left_memory_max_kib and reference_left_memory_high_kib (empty
#   when no cgroup the job leaves sets that limit).
reference_scope_placement() {
  local cgroup root target path component limit value kib
  local -a components
  reference_scope_slice=
  reference_left_memory_max_kib=
  reference_left_memory_high_kib=
  cgroup=$(sed -n 's/^0:://p' "/proc/$$/cgroup" 2>/dev/null) || cgroup=
  root=$(systemctl --user show --property=ControlGroup --value -- -.slice 2>/dev/null) || root=
  target=$root
  if [[ -n "$root" && "$cgroup" == "$root"/* ]]; then
    path=$root
    IFS=/ read -ra components <<<"${cgroup#"$root"/}"
    for component in "${components[@]}"; do
      path+=/$component
      if [[ "$component" == *.slice ]]; then
        reference_scope_slice=$component
        target=$path
      fi
    done
  fi
  path=
  IFS=/ read -ra components <<<"${cgroup#/}"
  for component in "${components[@]}"; do
    [[ -n "$component" ]] || continue
    path+=/$component
    if [[ -n "$target" && ("$target" == "$path" || "$target" == "$path"/*) ]]; then
      continue
    fi
    for limit in max high; do
      value=
      { read -r value <"/sys/fs/cgroup$path/memory.$limit"; } 2>/dev/null || true
      [[ "$value" =~ ^[0-9]+$ ]] || continue
      kib=$((value / 1024))
      if [[ "$limit" == max ]]; then
        if [[ -z "$reference_left_memory_max_kib" ]] || ((kib < reference_left_memory_max_kib)); then
          reference_left_memory_max_kib=$kib
        fi
      elif [[ -z "$reference_left_memory_high_kib" ]] || ((kib < reference_left_memory_high_kib)); then
        reference_left_memory_high_kib=$kib
      fi
    done
  done
}

# reference_enter_whole_job [ARGUMENT...]
#   Called first by every gate with its own arguments. It establishes the gate's process state once,
#   so that the gate's verdict depends on krust, the pinned reference and the case, and not on the
#   process that started the gate:
#   - standard input is /dev/null and no inherited descriptor above 2 stays open;
#   - GHCRTS is removed: every reference call sets the GHC runtime options of the binary it runs,
#     `${REFERENCE_GHCRTS--N1}` for a binary of the threaded runtime and none otherwise;
#   - the whole job runs in a new user systemd scope in its caller's slice, under memory limits no
#     larger than the guard's and than those of every cgroup it leaves (reference_scope_placement),
#     so the guard never loosens a memory limit, whether or not its caller is already bounded
#     (a left cgroup's CPU, task and runtime limits do not follow the job); without a user
#     manager it runs under an RLIMIT_AS ceiling no larger than the caller's.
#   It exports REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND (systemd-scope or rlimit-as) for the processes
#   the gate starts; it never reads that variable.
reference_enter_whole_job() {
  local script=${BASH_SOURCE[1]:-}
  local memory_high_kib=$reference_job_memory_high_kib
  local memory_max_kib=$reference_job_memory_max_kib
  local unit current
  local -a scope_options

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

  # systemd-run --scope execs the script again in this same process, inside the scope created
  # below. Only that exec carries this process's own PID here: a value inherited from a caller,
  # guarded or not, names another process, so it never skips the guard.
  if [[ "${REFERENCE_DIFFERENTIAL_JOB_GUARD_PROCESS:-}" == "$$" ]]; then
    unset REFERENCE_DIFFERENTIAL_JOB_GUARD_PROCESS
    reference_job_guard_kind=systemd-scope
    export REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND=$reference_job_guard_kind
    return 0
  fi
  unset REFERENCE_DIFFERENTIAL_JOB_GUARD_PROCESS REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND GHCRTS
  exec </dev/null
  reference_close_inherited_descriptors

  if [[ -z "$script" ]]; then
    echo "error: reference_enter_whole_job must be called from a differential script" >&2
    return 2
  fi
  if [[ "$script" != /* ]]; then
    script=$(cd "$(dirname "$script")" && pwd)/$(basename "$script")
  fi

  reference_scope_placement
  if [[ -n "$reference_left_memory_max_kib" ]] && ((reference_left_memory_max_kib < memory_max_kib)); then
    memory_max_kib=$reference_left_memory_max_kib
  fi
  if [[ -n "$reference_left_memory_high_kib" ]] && ((reference_left_memory_high_kib < memory_high_kib)); then
    memory_high_kib=$reference_left_memory_high_kib
  fi
  if ((memory_high_kib > memory_max_kib)); then
    memory_high_kib=$memory_max_kib
  fi
  # A unique name: a scope ended by the out-of-memory killer can stay loaded as failed, and the
  # caller's own scope may already carry the default name derived from this PID.
  unit=reference-gate-$$-${EPOCHREALTIME//[!0-9]/}
  scope_options=(
    --user --scope --quiet --collect
    ${reference_scope_slice:+"--slice=$reference_scope_slice"}
    -p "MemoryHigh=${memory_high_kib}K"
    -p "MemoryMax=${memory_max_kib}K"
    -p MemorySwapMax=0
  )
  # Probe separately so a nonzero command status is never mistaken for an
  # unavailable user manager and executed a second time through the fallback.
  if command -v systemd-run >/dev/null 2>&1 && \
    systemd-run "${scope_options[@]}" --unit="$unit-probe" -- true >/dev/null 2>&1; then
    export REFERENCE_DIFFERENTIAL_JOB_GUARD_PROCESS=$$
    exec systemd-run "${scope_options[@]}" --unit="$unit" -- "$BASH" "$script" "$@"
  fi

  current=$(ulimit -v)
  if [[ "$current" == unlimited ]] || ((current > reference_job_fallback_virtual_memory_kib)); then
    echo "warning: user systemd scopes unavailable; applying the $reference_job_fallback_virtual_memory_kib KiB whole-job virtual-address fallback (RLIMIT_AS), not a resident-memory limit" >&2
    if ! ulimit -v "$reference_job_fallback_virtual_memory_kib"; then
      echo "error: could not apply the whole-job virtual-address fallback" >&2
      return 2
    fi
  else
    echo "warning: user systemd scopes unavailable; keeping the caller's tighter $current KiB virtual-address limit (RLIMIT_AS) as the whole-job fallback, not a resident-memory limit" >&2
  fi
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
  reference_job_guard_kind=rlimit-as
  export REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND=$reference_job_guard_kind
}

# Runs a krust build or run of a gate. It needs the whole-job guard of this shell: a scope opened
# here would be a sibling of the job's scope, not a child, so the krust process is bounded only by
# the guard the gate entered.
reference_run_rust_frontend() {
  case ${reference_job_guard_kind:-} in
    systemd-scope | rlimit-as)
      "$@"
      ;;
    *)
      echo "error: reference_run_rust_frontend requires the whole-job memory guard" >&2
      return 2
      ;;
  esac
}
