"""Replay the standalone package in a fresh directory, using ordinary Python."""

from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile, time

if not __debug__:
    raise SystemExit("Run without -O")
ap = argparse.ArgumentParser()
ap.add_argument("--output", type=Path)
args = ap.parse_args()
source = Path(__file__).resolve().parent
names = [
    "rational_intervals.py",
    "exact_geometry.py",
    "verify_wholeball_mean.py",
    "enumerate_contact_maps_extended.py",
    "verify_packing.py",
    "verify_variance.py",
    "verify_sos_gap.py",
    "verify_tail124.py",
    "variance_witness.json",
    "sos_gap.witness.json",
]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
bindings = {n: sha(source / n) for n in names}
if args.output is None:
    dest = Path(tempfile.mkdtemp(prefix="tail124-standalone-"))
else:
    dest = args.output.resolve()
    dest.mkdir(parents=True, exist_ok=False)
for n in names:
    shutil.copyfile(source / n, dest / n)
env = os.environ.copy()
env.update(PYTHONDONTWRITEBYTECODE="1", OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1")
commands = [
    ["verify_packing.py"],
    ["verify_wholeball_mean.py"],
    ["verify_variance.py"],
    ["verify_sos_gap.py", "sos_gap.witness.json"],
    ["verify_tail124.py"],
]
record = {"status": "RUNNING", "source_sha256": bindings, "runs": []}
start = time.perf_counter()
for cmd in commands:
    t = time.perf_counter()
    log = dest / (cmd[0] + ".log")
    with log.open("w") as stream:
        r = subprocess.run(
            [sys.executable, *cmd],
            cwd=dest,
            env=env,
            stdout=stream,
            stderr=subprocess.STDOUT,
        )
    record["runs"].append(
        {
            "command": cmd,
            "exit_code": r.returncode,
            "elapsed_seconds": time.perf_counter() - t,
        }
    )
    print(cmd[0], r.returncode, flush=True)
    if r.returncode:
        record["status"] = "FAIL"
        (dest / "REPLAY.json").write_text(json.dumps(record, indent=2) + "\n")
        raise SystemExit(r.returncode)
for n, h in bindings.items():
    assert sha(source / n) == sha(dest / n) == h
record["status"] = "PASS_STANDALONE_REPLAY"
record["elapsed_seconds"] = time.perf_counter() - start
record["report_sha256"] = {
    p.name: sha(p) for p in dest.glob("*.json") if p.name not in names
}
(dest / "REPLAY.json").write_text(json.dumps(record, indent=2) + "\n")
print("PASS", dest, flush=True)
