#!/usr/bin/env python3
"""Synthetic escalation control: child inherits SIGINT ignored, TERM stays default."""
import signal,subprocess,sys,time
signal.signal(signal.SIGINT,signal.SIG_IGN)
child=subprocess.Popen(sys.argv[1:])
child.wait()
# If the child exits early, retain the supervisor until TERM to exercise the
# escalation policy; this is experiment code, not an Anneal scheduler.
while True:time.sleep(1)
