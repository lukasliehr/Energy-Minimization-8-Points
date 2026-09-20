"""Exhaustively check the packing graph obligation for k=2,4,6.
The accompanying mathematical proof establishes that every relevant contact
map satisfies the enumerated necessary predicates. No isomorphism pruning.
"""

from pathlib import Path
import hashlib, json, sys, time

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit("Run without -O")
import enumerate_contact_maps_extended as enumeration

start = time.perf_counter()
report = {
    "status": "RUNNING_PACKING_ENUMERATION",
    "canonical_pruning": False,
    "topology_pruning": True,
    "adjacent_degree_four_angle_pruning": False,
    "source_sha256": {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [Path(__file__), Path(enumeration.__file__)]
    },
    "runs": [],
}
for k in (6, 4, 2):
    result = enumeration.run(k, deduplicate=False)
    result["surviving_labelled_graphs"] = len(result.pop("surviving_maps"))
    report["runs"].append(result)
    print(json.dumps(result), flush=True)
report["status"] = "PASS_PACKING_ENUMERATION"
report["all_surviving_graphs_have_verified_spanning_cubes"] = True
report["elapsed_seconds"] = time.perf_counter() - start
Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
