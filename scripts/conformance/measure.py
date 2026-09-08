#!/usr/bin/env python3
"""Run a command, record wall time, peak RSS (max over descendants, via RUSAGE_CHILDREN), exit code.

Usage: measure.py --log PREFIX [--timeout SECS] -- cmd args...
Writes PREFIX.stdout, PREFIX.stderr, PREFIX.meta.toml.
Substitute for /usr/bin/time -v, which is not installed in the sandbox.
"""
import argparse, json, os, resource, subprocess, sys, time, signal

p = argparse.ArgumentParser()
p.add_argument("--log", required=True)
p.add_argument("--timeout", type=float, default=None)
p.add_argument("--cwd", default=None)
p.add_argument("cmd", nargs=argparse.REMAINDER)
a = p.parse_args()
cmd = a.cmd[1:] if a.cmd and a.cmd[0] == "--" else a.cmd
out = open(a.log + ".stdout", "wb")
err = open(a.log + ".stderr", "wb")
t0 = time.monotonic()
timed_out = False
proc = subprocess.Popen(cmd, stdout=out, stderr=err, cwd=a.cwd, start_new_session=True)
try:
    rc = proc.wait(timeout=a.timeout)
except subprocess.TimeoutExpired:
    timed_out = True
    os.killpg(proc.pid, signal.SIGKILL)
    rc = proc.wait()
wall = time.monotonic() - t0
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
with open(a.log + ".meta.toml", "w") as f:
    # JSON string escaping is also valid in TOML basic strings. Keep Unicode scalars
    # literal (JSON surrogate pairs are not TOML escapes), and escape TOML's DEL.
    command = json.dumps(cmd, ensure_ascii=False).replace('\x7f', '\\u007f')
    f.write(f"command = {command}\n")
    f.write(f"exit_code = {rc}\n")
    f.write(f"timed_out = {str(timed_out).lower()}\n")
    f.write(f"wall_seconds = {wall:.1f}\n")
    f.write(f"peak_rss_kib = {int(ru.ru_maxrss)}\n")
    f.write(f"peak_rss_mib = {ru.ru_maxrss / 1024:.0f}\n")
    f.write(f"user_seconds = {ru.ru_utime:.1f}\n")
    f.write(f"system_seconds = {ru.ru_stime:.1f}\n")
print(f"exit={rc} timed_out={timed_out} wall={wall:.1f}s rss={ru.ru_maxrss/1024:.0f}MiB", file=sys.stderr)
sys.exit(rc)
