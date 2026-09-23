#!/usr/bin/env python3
"""Run a command, record wall time, peak RSS (max over descendants, via RUSAGE_CHILDREN), exit code.

Usage: measure.py --log PREFIX [--timeout SECS] [--stdout-keep-bytes N [--stdout-check CHECK]] -- cmd args...
Writes PREFIX.stdout, PREFIX.stderr, PREFIX.meta.toml.
Substitute for /usr/bin/time -v, which is not installed in the sandbox.

With --stdout-keep-bytes, stdout goes through a pipe that this process reads as a stream
(stdout_stream.py): PREFIX.stdout is kept only while it is at most N bytes long, and otherwise
replaced by its first 64 KiB, PREFIX.stdout.head; meta.toml gains stdout_bytes, stdout_sha256
and stdout_kept. With --stdout-check, the stdout predicates of that check.json are evaluated on
the stream and written to PREFIX.stdout-check.json. The reader is a thread of this process, not
a child, so RUSAGE_CHILDREN (peak RSS, user and system time) still covers only the command; the
wall time ends when the command exits, before the reader finishes the last queued blocks. If
the reader fails, meta.toml has no stdout fields and measure.py exits 125.
"""
import argparse, fcntl, json, os, resource, subprocess, sys, threading, time, signal

import stdout_stream

p = argparse.ArgumentParser()
p.add_argument("--log", required=True)
p.add_argument("--timeout", type=float, default=None)
p.add_argument("--cwd", default=None)
p.add_argument("--stdout-keep-bytes", type=int, default=None)
p.add_argument("--stdout-check", default=None)
p.add_argument("cmd", nargs=argparse.REMAINDER)
a = p.parse_args()
cmd = a.cmd[1:] if a.cmd and a.cmd[0] == "--" else a.cmd
if a.stdout_check is not None and a.stdout_keep_bytes is None:
    p.error("--stdout-check requires --stdout-keep-bytes")
streamed = a.stdout_keep_bytes is not None
if streamed:
    sink = stdout_stream.ByteSink(a.log + ".stdout", a.stdout_keep_bytes)
    predicates = stdout_stream.load_predicates(a.stdout_check) if a.stdout_check else None
    out = subprocess.PIPE
else:
    out = open(a.log + ".stdout", "wb")
err = open(a.log + ".stderr", "wb")
t0 = time.monotonic()
timed_out = False
proc = subprocess.Popen(cmd, stdout=out, stderr=err, cwd=a.cwd, start_new_session=True)
if streamed:
    try:
        # A larger pipe lets the command run ahead of the reader by up to 1 MiB.
        fcntl.fcntl(proc.stdout.fileno(), fcntl.F_SETPIPE_SZ, 1 << 20)
    except OSError:
        pass
    reader_failure = []

    def read_stdout():
        try:
            stdout_stream.consume(proc.stdout.raw, sink, predicates)
        except BaseException as error:
            reader_failure.append(error)

    reader = threading.Thread(target=read_stdout)
    reader.start()
try:
    rc = proc.wait(timeout=a.timeout)
except subprocess.TimeoutExpired:
    timed_out = True
    os.killpg(proc.pid, signal.SIGKILL)
    rc = proc.wait()
wall = time.monotonic() - t0
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
if streamed:
    reader.join()
    proc.stdout.close()
    if reader_failure:
        print(f"error: reading the command's stdout failed: {reader_failure[0]!r}", file=sys.stderr)
    elif predicates is not None:
        with open(a.log + ".stdout-check.json", "w") as f:
            json.dump(predicates.results(), f)
            f.write("\n")
with open(a.log + ".meta.toml", "w") as f:
    # JSON string escaping is also valid in TOML basic strings. Keep Unicode scalars
    # literal (JSON surrogate pairs are not TOML escapes), and escape TOML's DEL.
    command = json.dumps(cmd, ensure_ascii=False).replace('\x7f', '\\u007f')
    f.write(f"command = {command}\n")
    f.write(f"exit_code = {rc}\n")
    f.write(f"timed_out = {str(timed_out).lower()}\n")
    f.write(f"wall_seconds = {wall:.3f}\n")
    f.write(f"peak_rss_kib = {int(ru.ru_maxrss)}\n")
    f.write(f"peak_rss_mib = {ru.ru_maxrss / 1024:.0f}\n")
    f.write(f"user_seconds = {ru.ru_utime:.1f}\n")
    f.write(f"system_seconds = {ru.ru_stime:.1f}\n")
    if streamed and not reader_failure:
        summary = sink.summary()
        f.write(f"stdout_bytes = {summary['bytes']}\n")
        f.write(f"stdout_sha256 = \"{summary['sha256']}\"\n")
        f.write(f"stdout_kept = {str(summary['kept']).lower()}\n")
print(f"exit={rc} timed_out={timed_out} wall={wall:.1f}s rss={ru.ru_maxrss/1024:.0f}MiB", file=sys.stderr)
sys.exit(125 if streamed and reader_failure else rc)
