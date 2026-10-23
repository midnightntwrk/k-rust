#!/usr/bin/env python3
"""rtime.py COMMAND...: run COMMAND, then print wall time, CPU time of all children and the
largest child's peak RSS to stderr (without depending on /usr/bin/time)."""
import resource, subprocess, sys, time
t = time.time()
rc = subprocess.call(sys.argv[1:])
u = resource.getrusage(resource.RUSAGE_CHILDREN)
print(f"rtime: wall {time.time() - t:.1f} s, cpu {u.ru_utime + u.ru_stime:.1f} s, "
      f"max child rss {u.ru_maxrss / 1024:.0f} MiB, exit {rc}", file=sys.stderr)
sys.exit(rc)
