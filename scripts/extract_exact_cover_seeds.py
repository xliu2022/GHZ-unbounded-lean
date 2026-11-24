#!/usr/bin/env python3
"""Extract the S6 printed tables and the S4 affine parameters deterministically."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
p = (root / "paper/supplement.tex").read_text()
results = {}
block = p[p.index(r"\subsection{Twelve vertices and fifteen vertices}"):
          p.index(r"\subsection{Thirteen perfect matchings on 18 vertices}")]
for n, d in [(12, 12), (15, 10)]:
    start = block.index(f"Edges on $[{n}]$")
    part = block[start:block.index(r"\bottomrule", start)]
    triples = [[int(x) - 1 for x in g]
               for g in re.findall(r"\$\((\d+),(\d+),(\d+)\)\$", part)]
    assert len(triples) == d * n // 3
    results[f"U{n}"] = {"n": n, "rows": [triples[i:i+n//3]
                        for i in range(0, len(triples), n//3)]}
b = p[p.index(r"\subsection{Thirteen perfect matchings on 18 vertices}"):
      p.index(r"\subsection{Ten perfect matchings on 21 vertices}")]
b = b[b.index(r"\begin{array}"):b.index(r"\end{array}")]
base = re.findall(r"(\d{3})(?:\^\{(\d+)\})?", b)
assert len(base) == 39
rows = []
for r in range(13):
    row = []
    for triple, shift in base[3*r:3*r+3]:
        for layer in range(2):
            row.append([2*int(v)+(layer+(v in shift)) % 2 for v in triple])
    rows.append(row)
results["U18"] = {"n": 18, "rows": rows}
b = p[p.index(r"\subsection{Ten perfect matchings on 21 vertices}"):
      p.index(r"\subsection{Ten perfect matchings on 24 vertices}")]
triples = [list(map(int, g)) for g in re.findall(r"\\\{(\d+),(\d+),(\d+)\\\}", b)]
assert len(triples) == 70
results["U21"] = {"n": 21, "rows": [triples[i:i+7] for i in range(0, 70, 7)]}
start = p.index(r"\subsection{Ten perfect matchings on 24 vertices}")
stop = p.index(r"\subsection{Ten perfect matchings on \texorpdfstring", start)
b = p[start:stop]
b = b[b.index(r"\begin{array}"):b.index(r"\end{array}")]
base = re.findall(r"\\\{(\d+(?:,\d+)*)\\\}(?:\^\{\\\{(\d+(?:,\d+)*)\\\}\})?", b)
assert len(base) == 40
rows = []
for r in range(10):
    row = []
    for triple, shift in base[4*r:4*r+4]:
        triple = list(map(int, triple.split(',')))
        shift = set(map(int, shift.split(','))) if shift else set()
        for layer in range(2):
            row.append([12*((layer+(v in shift)) % 2)+v-1 for v in triple])
    rows.append(row)
results["U24"] = {"n": 24, "rows": rows}
affine = [(3, 1, [0, 1, 2]), (5, 1, [0, 1, 2, 3]), (7, 1, [0, 1, 2, 3]),
          (11, 2, [0, 1, 2, 3, 5]), (13, 2, [0, 1, 2, 4, 5, 8]),
          (17, 2, [0, 1, 2, 4, 5]), (19, 3, [0, 1, 3, 12, 14, 15]),
          (23, 2, [0, 1, 2, 9, 10, 11]), (29, 8, [0, 1, 2, 7, 20, 21]),
          (31, 4, [0, 1, 3, 16, 21, 28]), (37, 1, [0, 1, 2, 5, 21]),
          (41, 1, [0, 1, 2, 5, 16]), (43, 1, [0, 1, 2, 5, 38]),
          (47, 1, [0, 1, 2, 11, 23])]
for m, lam, shifts in affine:
    rows = [[[a, m+(lam*a+s) % m, 2*m+(-(lam+1)*a-s) % m]
             for a in range(m)] for s in shifts]
    results[f"A{m}"] = {"n": 3*m, "m": m, "lam": lam, "shifts": shifts, "rows": rows}
for name, data in results.items():
    n, rows = data['n'], data['rows']
    edges = [tuple(sorted(e)) for row in rows for e in row]
    assert len(set(edges)) == len(edges), name
    assert all(sorted(v for edge in row for v in edge) == list(range(n))
               for row in rows), name
    print(name, "vertices", n, "edges", len(edges), "prescribed", len(rows))
out = root / "RigidGHZ/Finite/ExactCoverCertificates/seeds.json"
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(results, indent=2) + '\n')
