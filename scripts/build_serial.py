#!/usr/bin/env python3
"""Prebuild local Lean modules in dependency order with one Lake target at a time.

This limits concurrency on machines with modest memory. By default it schedules
modules whose local source/dependency timestamps predict a missing or stale
Lake trace, then runs the full authoritative build. The timestamp heuristic is
only a scheduling optimization: Lake still validates its own build traces.
The default scope is the three primary Solution/Challenge pairs. Use --all
for an explicitly serial visit of every module in that scope; add
--include-supplement to build the entire retained development.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time

from check_source import without_comments

ROOT = Path(__file__).resolve().parents[1]
PRIMARY_ROOTS = ["Solution", "FiniteSolution", "PhysicsSolution", "Challenge",
                 "FiniteChallenge", "PhysicsChallenge"]
FULL_ROOTS = ["RigidGHZ", *PRIMARY_ROOTS, "SupplementChallenge", "SupplementSolution"]


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--include-supplement", action="store_true",
                    help="also prebuild and build the retained supplementary development")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--no-final-build", action="store_true")
    ns = ap.parse_args()
    paths = list((ROOT / "RigidGHZ").rglob("*.lean")) + list(ROOT.glob("*.lean"))
    paths = [p for p in paths if p.name != "lakefile.lean"]
    modules = {".".join(p.relative_to(ROOT).with_suffix("").parts): p for p in paths}
    dependencies = {}
    for name, p in modules.items():
        imports = re.findall(r"^\s*(?:public\s+)?import\s+([\w.]+)",
                             without_comments(p.read_text()), re.M)
        dependencies[name] = [n for n in imports if n in modules]
    order, active, done = [], set(), set()

    def visit(name: str) -> None:
        if name in done:
            return
        if name in active:
            raise SystemExit(f"Local import cycle at {name}")
        active.add(name)
        for dependency in dependencies[name]:
            visit(dependency)
        active.remove(name)
        done.add(name)
        order.append(name)

    roots = FULL_ROOTS if ns.include_supplement else PRIMARY_ROOTS
    for name in sorted(modules) if ns.include_supplement else roots:
        visit(name)
    scheduled = set()
    for name in order:
        base = ROOT / ".lake/build/lib/lean" / name.replace(".", "/")
        trace, olean = base.with_suffix(".trace"), base.with_suffix(".olean")
        stale = not trace.exists() or not olean.exists()
        if not stale:
            stale = modules[name].stat().st_mtime_ns > trace.stat().st_mtime_ns
        if ns.all or stale or any(n in scheduled for n in dependencies[name]):
            scheduled.add(name)
    selected = [name for name in order if name in scheduled]
    if ns.list:
        print("\n".join(selected))
        print(f"{len(selected)} scheduled / {len(order)} local modules in selected scope")
        return
    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    env["LEAN_NUM_THREADS"] = "1"
    logdir = ROOT / ".lake/verification/serial-build"
    logdir.mkdir(parents=True, exist_ok=True)
    record = {"kind": "serial-local-build", "lean_num_threads": 1,
              "scope": "full-development" if ns.include_supplement else "primary",
              "roots": roots,
              "targets": [], "passed": False}

    def run(label: str, args: list[str]) -> None:
        start = time.monotonic()
        with (logdir / (label + ".log")).open("w") as log:
            p = subprocess.run(args, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        record["targets"].append({"name": label, "returncode": p.returncode,
                                  "seconds": round(time.monotonic() - start, 3)})
        (logdir / "report.json").write_text(json.dumps(record, indent=2) + "\n")
        print(f"{label}: exit {p.returncode}; {record['targets'][-1]['seconds']} s", flush=True)
        if p.returncode:
            print((logdir / (label + ".log")).read_text()[-15000:], flush=True)
            raise SystemExit(p.returncode)

    for index, name in enumerate(selected, 1):
        print(f"[{index}/{len(selected)}]", end=" ", flush=True)
        run(name, ["lake", "--no-cache", "build", "+" + name])
    if not ns.no_final_build:
        run("full-build", ["lake", "--no-cache", "build", *roots])
    record["passed"] = True
    (logdir / "report.json").write_text(json.dumps(record, indent=2) + "\n")
    evidence = ROOT / "verification/serial-build-report.json"
    evidence.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Build passed. Report: {evidence}")


if __name__ == "__main__":
    main()
