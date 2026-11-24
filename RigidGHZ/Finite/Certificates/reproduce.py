#!/usr/bin/env python3
"""Reproduce the finite CNF, clause metadata, and pruned LRAT certificates.

No output of this program is trusted by Lean.  The semantic bridge proves every
initial clause about the ordinary hypergraph definitions.  SatLRATChunk then
reconstructs each LRAT inference as a theorem checked by Lean's kernel.

Examples:
  python3 reproduce.py generate --out /tmp/rigid-nine-certificates
  python3 reproduce.py solve --out /tmp/rigid-nine-certificates --cadical PATH
  python3 reproduce.py prune --out /tmp/rigid-nine-certificates
  python3 reproduce.py hashes --out /tmp/rigid-nine-certificates

The recorded traces used CaDiCaL 2.1.2, bundled with Lean 4.35.0-rc2, with
--lrat --no-binary.  A different solver version may produce a different valid
trace; it must still pass the same Lean reconstruction.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from itertools import combinations
from pathlib import Path


CASES = ("4a", "4b", "5a", "5b", "6a", "7")
GIVEN = {
    "4a": ((3, 4, 5), (6, 7, 8)),
    "4b": ((3, 4, 6), (5, 7, 8)),
    "5a": ((3, 7, 8), (4, 5, 6)),
    "5b": ((3, 4, 7), (5, 6, 8)),
    "6a": ((3, 4, 8), (5, 6, 7)),
}


def generate(out: Path) -> None:
    edges = list(combinations(range(9), 3))
    edge_index = {edge: i for i, edge in enumerate(edges)}
    partitions = []
    for edge in edges:
        rest = set(range(9)) - set(edge)
        for second in combinations(sorted(rest), 3):
            third = tuple(sorted(rest - set(second)))
            if edge < second < third:
                partitions.append(tuple(edge_index[e] for e in (edge, second, third)))
    assert len(edges) == 84 and len(partitions) == 280
    clauses, metadata = [], []

    def add(clause, kind, *args):
        clauses.append(clause)
        metadata.append([kind, *args])

    def ev(e):
        return e + 1

    def pv(p):
        return 85 + p

    def cv(v, i, k):
        return 365 + v * 464 + i * 16 + k

    for p, es in enumerate(partitions):
        for s, e in enumerate(es):
            add([-pv(p), ev(e)], "forward", p, s)
        add([pv(p), *(-ev(e) for e in es)], "backward", p)
    for e in range(84):
        ps = [i for i, p in enumerate(partitions) if e in p]
        add([-ev(e), *(pv(i) for i in ps)], "cover", e)
        for k, (i, j) in enumerate(combinations(ps, 2)):
            add([-pv(i), -pv(j)], "conflict", e, k)
    for v in range(9):
        es = [i for i, e in enumerate(edges) if v in e]
        for i in range(29):
            add([cv(v, i, 0)], "zero", v, i)
        for k in range(1, 16):
            add([-cv(v, 0, k)], "empty", v, k - 1)
        for i, e in enumerate(es):
            for k in range(15):
                a, b, x, y = cv(v, i, k + 1), cv(v, i, k), ev(e), cv(v, i + 1, k + 1)
                add([-a, y], "step1", v, i, k)
                add([-x, -b, y], "step2", v, i, k)
                add([-y, a, x], "step3", v, i, k)
                add([-y, a, b], "step4", v, i, k)
        add([cv(v, 28, 14)], "lower", v)
        add([-cv(v, 28, 15)], "upper", v)
    for case in CASES:
        k = int(case[0])
        cs, ms = clauses.copy(), metadata.copy()
        for j in range(7):
            cs.append([ev(j) * (1 if j < k else -1)])
            ms.append(["normpos" if j < k else "normneg", j])
        if k == 4:
            fan = 0
            for a, b in combinations(range(9), 2):
                for xs in combinations([x for x in range(9) if x not in (a, b)], 5):
                    cs.append([-ev(edge_index[tuple(sorted((a, b, x)))]) for x in xs])
                    ms.append(["fan", fan])
                    fan += 1
            assert fan == 756
        for j, edge in enumerate(GIVEN.get(case, ())):
            e = edge_index[edge]
            cs.append([ev(e)])
            ms.append(["given", j, e])
        (out / f"nine{case}.cnf").write_text(
            f"p cnf 4540 {len(cs)}\n"
            + "".join(" ".join(map(str, c)) + " 0\n" for c in cs)
        )
        (out / f"nine{case}.json").write_text(json.dumps(ms, separators=(",", ":")))


def solve(out: Path, cadical: str) -> None:
    for case in CASES:
        with (out / f"nine{case}.solver.log").open("w") as log:
            result = subprocess.run(
                [cadical, "--lrat", "--no-binary", str(out / f"nine{case}.cnf"),
                 str(out / f"nine{case}.lrat")], stdout=log, stderr=subprocess.STDOUT
            )
        if result.returncode != 20:
            raise RuntimeError(f"case {case}: solver exit {result.returncode}; expected UNSAT (20)")


def prune(out: Path) -> None:
    for case in CASES:
        lines = (out / f"nine{case}.cnf").read_text().splitlines()
        nvars, count = map(int, lines.pop(0).split()[2:])
        metadata = json.loads((out / f"nine{case}.json").read_text())
        proofs, order, last = {}, [], None
        for line in (out / f"nine{case}.lrat").read_text().splitlines():
            tokens = line.split()
            if tokens[1] == "d":
                continue
            values = list(map(int, tokens))
            clause_id, end = values[0], values.index(0)
            literals, hints = values[1:end], values[end + 1:-1]
            if not all(h > 0 for h in hints):
                raise ValueError("Only RUP traces with positive LRAT hints are supported")
            proofs[clause_id] = literals, hints
            order.append(clause_id)
            if not literals:
                last = clause_id
        if last is None:
            raise ValueError("Trace contains no empty clause")
        needed, stack = set(), [last]
        while stack:
            clause_id = stack.pop()
            if clause_id in needed:
                continue
            needed.add(clause_id)
            if clause_id > count:
                stack.extend(proofs[clause_id][1])
        inputs = sorted(i for i in needed if i <= count)
        derived = [i for i in order if i in needed]
        rename = {old: new + 1 for new, old in enumerate(inputs + derived)}
        (out / f"core{case}.cnf").write_text(
            f"p cnf {nvars} {len(inputs)}\n" + "".join(lines[i - 1] + "\n" for i in inputs)
        )
        (out / f"core{case}.json").write_text(
            json.dumps([metadata[i - 1] for i in inputs], separators=(",", ":"))
        )
        with (out / f"core{case}.lrat").open("w") as trace:
            for clause_id in derived:
                literals, hints = proofs[clause_id]
                trace.write(" ".join(map(str, [rename[clause_id], *literals, 0,
                                                *(rename[h] for h in hints), 0])) + "\n")
        print(case, "initial clauses", len(inputs), "derived clauses", len(derived))


def hashes(out: Path) -> None:
    for case in CASES:
        for suffix in ("cnf", "json", "lrat"):
            path = out / f"core{case}.{suffix}"
            print(hashlib.sha256(path.read_bytes()).hexdigest(), path.name)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("generate", "solve", "prune", "hashes"))
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--cadical", default="cadical")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.action == "solve":
        solve(args.out, args.cadical)
    else:
        globals()[args.action](args.out)


if __name__ == "__main__":
    main()
