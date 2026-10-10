#!/usr/bin/env bash
# The listening port of a server a gate started, read from the server itself.
#
# A gate starts each RPC server with `--server-port 0` (unless the caller pins a port), so the
# kernel assigns a free port at the server's own bind: two concurrent gate runs cannot be given
# the same port, and there is no window between choosing a port and binding it. The pinned
# reference servers do not print the port they bound, so the gate reads it from the TCP socket
# in LISTEN state among the server's own open file descriptors (/proc/PID/fd against
# /proc/net/tcp and /proc/net/tcp6). That also proves the gate talks to the server it started,
# never to another process listening on the same port. Linux only, like the gates' memory guard.

# reference_server_process_tree PID
#   Prints PID and every process descended from it, one per line (a wrapper may fork the server
#   rather than exec it).
reference_server_process_tree() {
  local pid=$1
  local child
  echo "$pid"
  for child in $(cat /proc/"$pid"/task/*/children 2>/dev/null); do
    reference_server_process_tree "$child"
  done
}

# reference_server_port PID
#   Prints the port of the one TCP socket in LISTEN state held open by PID or a descendant and not
#   by the gate's own shell. A socket the gate also holds was not bound by the server: the server
#   inherited it from the gate, which had it from its caller. reference_enter_whole_job closes such
#   descriptors before any server starts; this filter keeps the helper right without that.
#   Returns 1 while there is none, and 2 when there are several ports (the server is ambiguous).
reference_server_port() {
  local pid=$1
  local process descriptor target
  local -a inodes=() ports=()
  local -A inherited=()
  for descriptor in "/proc/$$/fd/"*; do
    target=$(readlink "$descriptor" 2>/dev/null) || continue
    if [[ "$target" =~ ^socket:\[([0-9]+)\]$ ]]; then
      inherited[${BASH_REMATCH[1]}]=1
    fi
  done
  for process in $(reference_server_process_tree "$pid"); do
    for descriptor in /proc/"$process"/fd/*; do
      target=$(readlink "$descriptor" 2>/dev/null) || continue
      if [[ "$target" =~ ^socket:\[([0-9]+)\]$ ]] && [[ -z "${inherited[${BASH_REMATCH[1]}]:-}" ]]; then
        inodes+=("${BASH_REMATCH[1]}")
      fi
    done
  done
  if ((${#inodes[@]} == 0)); then
    return 1
  fi
  # Columns of /proc/net/tcp{,6}: local_address is IP:PORT (PORT in hex), st 0A is LISTEN,
  # and the tenth column is the socket's inode.
  mapfile -t ports < <(
    awk -v inodes="${inodes[*]}" '
      BEGIN { count = split(inodes, list, " "); for (i = 1; i <= count; i++) owned[list[i]] = 1 }
      FNR > 1 && $4 == "0A" && ($10 in owned) { n = split($2, address, ":"); print address[n] }
    ' /proc/net/tcp /proc/net/tcp6 2>/dev/null | sort -u
  )
  case ${#ports[@]} in
    0) return 1 ;;
    1) printf '%d\n' "0x${ports[0]}" ;;
    *)
      echo "error: server process $pid listens on several ports: ${ports[*]} (hex)" >&2
      return 2
      ;;
  esac
}

# reference_wait_for_server_port PID LOG REQUESTED [ATTEMPTS]
#   Waits until server PID listens, then sets reference_listening_port to its port. REQUESTED
#   is the port the server was told to bind: 0 for any, or a port the caller pinned, which the
#   listening socket must then use. Fails, printing LOG, when the server exits first (for a
#   pinned port already in use, its bind fails) or does not listen within ATTEMPTS tenths of a
#   second (default 600).
# shellcheck disable=SC2034  # the gate scripts that source this file read reference_listening_port
reference_wait_for_server_port() {
  local pid=$1
  local log=$2
  local requested=$3
  local attempts=${4:-600}
  local attempt port status
  reference_listening_port=
  for ((attempt = 1; attempt <= attempts; attempt++)); do
    status=0
    port=$(reference_server_port "$pid") || status=$?
    if ((status == 0)); then
      if [[ "$requested" != 0 && "$port" != "$requested" ]]; then
        echo "error: server process $pid listens on port $port, not the requested $requested" >&2
        return 1
      fi
      reference_listening_port=$port
      return 0
    fi
    if ((status == 2)); then
      cat "$log" >&2
      return 1
    fi
    if ! kill -0 "$pid" 2>/dev/null; then
      echo "error: server process $pid exited before listening (requested port $requested)" >&2
      cat "$log" >&2
      return 1
    fi
    sleep 0.1
  done
  echo "error: server process $pid did not listen (requested port $requested)" >&2
  cat "$log" >&2
  return 1
}
