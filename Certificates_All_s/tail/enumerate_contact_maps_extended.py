"""Finite combinatorial exploration; geometric completeness requires an audit.

Enumerates all labelled graphs with a prescribed degree sequence, then all
triangle/quad sphere maps that meet necessary local angle conditions.
Uses only Python's standard library. It does not certify a Riesz interval.
"""

import itertools as it
import json
import time
from pathlib import Path

N = 8
PAIRS = tuple(it.combinations(range(N), 2))


def canonical(adj, trideg):
    colors = [(len(adj[i]), trideg[i]) for i in range(N)]
    while True:
        ids = {x: j for j, x in enumerate(sorted(set(colors)))}
        old = [ids[x] for x in colors]
        new = [(old[i], tuple(sorted(old[j] for j in adj[i]))) for i in range(N)]
        ids = {x: j for j, x in enumerate(sorted(set(new)))}
        refined = [ids[x] for x in new]
        if len(set(refined)) == len(set(old)):
            colors = refined
            break
        colors = new
    parts = [[i for i in range(N) if colors[i] == c] for c in sorted(set(colors))]
    best = None
    for choices in it.product(*(it.permutations(p) for p in parts)):
        order = sum((tuple(p) for p in choices), ())
        code = sum(
            (1 << k) for k, (i, j) in enumerate(PAIRS) if order[j] in adj[order[i]]
        )
        best = code if best is None else min(best, code)
    return tuple(len(p) for p in parts), best


def cycle_key(c):
    c = tuple(c)
    rev = c[::-1]
    return min(
        *(c[i:] + c[:i] for i in range(len(c))),
        *(rev[i:] + rev[:i] for i in range(len(c)))
    )


def edge(a, b):
    return tuple(sorted((a, b)))


def face_edges(f):
    return tuple(edge(f[i], f[(i + 1) % len(f)]) for i in range(len(f)))


def sphere_map(faces, adj):
    """Check edge use twice, cyclic links, consistent orientation and Euler=2."""
    uses = {}
    for fi, f in enumerate(faces):
        for i, a in enumerate(f):
            b = f[(i + 1) % len(f)]
            uses.setdefault(edge(a, b), []).append((fi, 1 if a < b else -1))
    if set(uses) != {edge(i, j) for i in range(N) for j in adj[i]}:
        return False
    if any(len(v) != 2 for v in uses.values()):
        return False
    if N - len(uses) + len(faces) != 2:
        return False
    for v in range(N):
        links = {w: [] for w in adj[v]}
        for f in faces:
            if v in f:
                i = f.index(v)
                a, b = f[i - 1], f[(i + 1) % len(f)]
                links[a].append(b)
                links[b].append(a)
        if any(len(ws) != 2 for ws in links.values()):
            return False
        visited, stack = set(), [next(iter(links))]
        while stack:
            w = stack.pop()
            if w not in visited:
                visited.add(w)
                stack.extend(links[w])
        if visited != set(links):
            return False
    orient = {0: 1}
    pending = [0]
    neighbors = {i: [] for i in range(len(faces))}
    for (i, si), (j, sj) in uses.values():
        neighbors[i].append((j, -si * sj))
        neighbors[j].append((i, -si * sj))
    while pending:
        i = pending.pop()
        for j, sign in neighbors[i]:
            want = orient[i] * sign
            if j in orient and orient[j] != want:
                return False
            if j not in orient:
                orient[j] = want
                pending.append(j)
    return len(orient) == len(faces)


def maps_for_graph(adj, triangles, trideg):
    edges = tuple(edge(i, j) for i in range(N) for j in adj[i] if i < j)
    need = {e: 2 for e in edges}
    for f in triangles:
        for e in face_edges(f):
            need[e] -= 1
    if min(need.values()) < 0:
        return []

    def kind(v):
        if len(adj[v]) == 4:
            return "equal" if trideg[v] == 3 else "low"
        return "high" if trideg[v] == 1 else "unknown"

    quads = set()
    for c in it.permutations(range(N), 4):
        if all(c[(i + 1) % 4] in adj[c[i]] for i in range(4)):
            # A contact diagonal would split the alleged face into triangles.
            if c[2] in adj[c[0]] or c[3] in adj[c[1]]:
                continue
            kinds = [kind(v) for v in c]
            if any(
                kinds[i] != kinds[i + 2] and "unknown" not in (kinds[i], kinds[i + 2])
                for i in (0, 1)
            ):
                continue
            quads.add(cycle_key(c))
    quads = sorted(quads)
    qe = [face_edges(q) for q in quads]
    byedge = {e: [i for i, es in enumerate(qe) if e in es] for e in edges}
    solutions, seen = [], set()

    def rec(selected):
        if not any(need.values()):
            key = tuple(sorted(selected))
            if key in seen:
                return
            seen.add(key)
            faces = list(triangles) + [quads[i] for i in key]
            if sphere_map(faces, adj):
                solutions.append(faces)
            return
        candidates = []
        for e, count in need.items():
            if count:
                options = [
                    i
                    for i in byedge[e]
                    if i not in selected and all(need[x] > 0 for x in qe[i])
                ]
                if len(options) < count:
                    return
                candidates.append((len(options), e, options))
        _, _, options = min(candidates)
        for i in options:
            for e in qe[i]:
                need[e] -= 1
            rec(selected + [i])
            for e in qe[i]:
                need[e] += 1

    rec([])
    return solutions


def cube_deletions(adj):
    four = {v for v in range(N) if len(adj[v]) == 4}
    eligible = [e for e in PAIRS if set(e) <= four and e[1] in adj[e[0]]]
    witnesses = []
    for removed in it.combinations(eligible, len(four) // 2):
        if sorted(v for e in removed for v in e) != sorted(four):
            continue
        residual = [set(ws) for ws in adj]
        for a, b in removed:
            residual[a].remove(b)
            residual[b].remove(a)
        if any(len(ws) != 3 for ws in residual):
            continue
        colors, stack, ok = {0: 0}, [0], True
        while stack:
            v = stack.pop()
            for w in residual[v]:
                if w in colors and colors[w] == colors[v]:
                    ok = False
                if w not in colors:
                    colors[w] = 1 - colors[v]
                    stack.append(w)
        if ok and len(colors) == N and sum(colors.values()) == 4:
            # Simple cubic bipartite 4+4 is exactly K4,4 minus a matching.
            witnesses.append([list(e) for e in removed])
    return witnesses


def run(k, deduplicate=True):
    target = [3] * k + [4] * (N - k)
    remaining = target.copy()
    adj = [set() for _ in range(N)]
    counts = dict(
        labelled_graphs=0, triangle_filtered=0, processed_graphs=0, sphere_maps=0
    )
    seen = set()
    records = []
    started = time.monotonic()

    def inspect():
        counts["labelled_graphs"] += 1
        triangles = [
            c
            for c in it.combinations(range(N), 3)
            if c[1] in adj[c[0]] and c[2] in adj[c[0]] and c[2] in adj[c[1]]
        ]
        if len(triangles) != 8 - k:
            return
        trideg = [sum(i in tri for tri in triangles) for i in range(N)]
        if any(trideg[i] > (1 if target[i] == 3 else 3) for i in range(N)):
            return
        if any(
            all(b in adj[a] for a, b in it.combinations(c, 2))
            for c in it.combinations(range(N), 4)
        ):
            return
        counts["triangle_filtered"] += 1
        if deduplicate:
            key = canonical(adj, trideg)
            if key in seen:
                return
            seen.add(key)
        counts["processed_graphs"] += 1
        maps = maps_for_graph(adj, triangles, trideg)
        counts["sphere_maps"] += len(maps)
        if maps:
            deletions = cube_deletions(adj)
            if not deletions:
                raise RuntimeError("A surviving map has no spanning cube")
            records.append(
                dict(
                    edges=[list(e) for e in PAIRS if e[1] in adj[e[0]]],
                    triangle_degrees=trideg,
                    maps=maps,
                    spanning_cube_deletions=deletions,
                )
            )

    def generate(i):
        if i == N:
            if not any(remaining):
                inspect()
            return
        d = remaining[i]
        available = [j for j in range(i + 1, N) if remaining[j] > 0]
        if d < 0 or len(available) < d:
            return
        for ns in it.combinations(available, d):
            remaining[i] = 0
            for j in ns:
                remaining[j] -= 1
                adj[i].add(j)
                adj[j].add(i)
            if all(0 <= remaining[j] <= N - i - 2 for j in range(i + 1, N)):
                generate(i + 1)
            for j in ns:
                remaining[j] += 1
                adj[i].remove(j)
                adj[j].remove(i)
            remaining[i] = d

    generate(0)
    return dict(
        k=k,
        deduplicate=deduplicate,
        counts=counts,
        elapsed_seconds=time.monotonic() - started,
        surviving_maps=records,
    )


if __name__ == "__main__":
    report = {"status": "combinatorial exploration; audit pending", "runs": []}
    output = Path(__file__).with_suffix(".json")
    for k in (6, 4, 2):
        result = run(k)
        report["runs"].append(result)
        output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(
            json.dumps(
                {
                    name: value
                    for name, value in result.items()
                    if name != "surviving_maps"
                }
            ),
            flush=True,
        )
