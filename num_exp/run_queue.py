"""Simple job queue for one workstation.

Jobs file format, one job per line (# comments allowed):
    <threads> <mem_GB> <command ...>
Jobs are started in the given order (put expensive ones first) whenever enough cores and (estimated) memory
are free. Each job gets its own log in logs/, wrapped in /usr/bin/time -v to record wall time and peak memory.
Finished jobs are recorded in logs/queue_done.txt, so a restarted queue skips them.
"""
import subprocess, sys, time, os, re

jobsfile = sys.argv[1]
max_cores = int(sys.argv[2]) if len(sys.argv) > 2 else 24
# budget for the sum of the (pessimistic, peak) memory estimates of running jobs; additionally, a job only
# starts if the currently available memory covers its estimate
max_mem = float(sys.argv[3]) if len(sys.argv) > 3 else 56.

def mem_available():
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable"):
            return float(line.split()[1]) / 1024**2
    return 0.

os.makedirs("logs", exist_ok=True)
donefile = "logs/queue_done.txt"
done = set(open(donefile).read().splitlines()) if os.path.exists(donefile) else set()

jobs = []
for line in open(jobsfile):
    line = line.strip()
    if not line or line.startswith("#"):
        continue
    thr, mem, cmd = line.split(maxsplit=2)
    if cmd in done:
        continue
    jobs.append((int(thr), float(mem), cmd))

def logname(cmd):
    return "logs/" + re.sub(r"[^A-Za-z0-9_.=-]+", "_", cmd.replace("python conv_study.py", "")).strip("_")[:150] + ".log"

running = []
print("{} jobs queued".format(len(jobs)), flush=True)
while jobs or running:
    for r in running[:]:
        if r[0].poll() is not None:
            running.remove(r)
            status = "ok" if r[0].returncode == 0 else "FAILED({})".format(r[0].returncode)
            print(time.strftime("%H:%M:%S"), status, r[3], flush=True)
            if r[0].returncode == 0:
                with open(donefile, "a") as fh:
                    fh.write(r[3] + "\n")
    used_c = sum(r[1] for r in running)
    used_m = sum(r[2] for r in running)
    # start the first job that fits (keeps the order as priority, but backfills with smaller jobs)
    for j in jobs[:]:
        thr, mem, cmd = j
        if used_c + thr <= max_cores and ((used_m + mem <= max_mem and mem + 4 <= mem_available()) or not running):
            p = subprocess.Popen("/usr/bin/time -v " + cmd, shell=True, stdout=open(logname(cmd), "w"),
                                 stderr=subprocess.STDOUT)
            running.append((p, thr, mem, cmd))
            jobs.remove(j)
            used_c += thr
            used_m += mem
            print(time.strftime("%H:%M:%S"), "start", cmd, flush=True)
    time.sleep(5)
print("all done", flush=True)
