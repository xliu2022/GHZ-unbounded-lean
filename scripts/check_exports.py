#!/usr/bin/env python3
"""Local export checks; not a replacement for Palomar's isolated full preflight.

Uses the toolchain's unchanged Comparator comparison and axiom-check functions,
then Lean's kernel and NanoDa on the same fresh proof export. All derived output
stays under .lake. No sandbox setting is changed by this script.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat",
    "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam",
]


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("config", nargs="?", default="comparator.json")
    ap.add_argument("--skip-build", action="store_true")
    ap.add_argument("--try-con-ron", action="store_true")
    ap.add_argument("--threads", type=int, default=1,
                    help="NanoDa worker threads; one limits peak memory for large finite proofs")
    ns = ap.parse_args()
    if ns.threads < 1:
        ap.error("--threads must be positive")
    os.chdir(ROOT)
    lake = shutil.which("lake")
    if lake is None:
        candidate = Path.home() / ".elan/bin/lake"
        lake = str(candidate) if candidate.exists() else None
    if lake is None:
        raise SystemExit("lake must be installed and available")
    prefix = Path(subprocess.check_output([lake, "env", "lean", "--print-prefix"],
                                          text=True).strip())
    lake_shared = prefix / "lib/lean/libLake_shared.so"
    config_path = ROOT / ns.config
    config = json.loads(config_path.read_text())
    out = ROOT / ".lake/verification" / config_path.stem
    out.mkdir(parents=True, exist_ok=True)
    report = {"configuration": ns.config, "kind": "local-export-diagnostics",
              "palomar_full_preflight": False, "checks": []}

    def run(name: str, cmd: list[str], *, output: Path | None = None,
            required: bool = True) -> None:
        print(f"Running {name}", flush=True)
        start = time.monotonic()
        log = out / f"{name}.log"
        with log.open("wb") as err:
            if output is None:
                proc = subprocess.run(cmd, stdout=err, stderr=subprocess.STDOUT)
            else:
                with output.open("wb") as dst:
                    proc = subprocess.run(cmd, stdout=dst, stderr=err)
        result = {"name": name, "returncode": proc.returncode,
                  "elapsed_seconds": round(time.monotonic() - start, 3),
                  "log": str(log.relative_to(ROOT))}
        report["checks"].append(result)
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"{name}: exit {proc.returncode} ({result['elapsed_seconds']} s)", flush=True)
        if proc.returncode and required:
            print(log.read_text(errors="replace")[-12000:], flush=True)
            raise SystemExit(proc.returncode)

    if not ns.skip_build:
        run("build", [lake, "--no-cache", "build", config["challenge_module"],
                      config["solution_module"]])
    names = list(dict.fromkeys(
        ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] + config["theorem_names"] +
        config["permitted_axioms"] + PRIMITIVES + config.get("definition_names", [])))
    exports = {}
    for side in ["challenge", "solution"]:
        path = out / f"{side}.ndjson"
        run(f"export-{side}", [lake, "env", "leanexport", config[f"{side}_module"],
                              "--", *names], output=path)
        exports[side] = path
        digest = hashlib.file_digest(path.open("rb"), "sha256").hexdigest()
        report[f"{side}_sha256"] = digest
        report[f"{side}_bytes"] = path.stat().st_size
    run("compare-and-axioms", [lake, "env", "lean", "-j", "1",
                              f"--load-dynlib={lake_shared}", "--run", "scripts/LocalCompare.lean",
                              str(config_path), str(exports["challenge"]), str(exports["solution"])])
    run("lean-kernel", [lake, "env", "leanchecker", "--silent", "--from-export",
                        str(exports["solution"])])
    nanoda_config = out / "nanoda.json"
    nanoda_config.write_text(json.dumps({
        "use_stdin": False, "export_file_path": str(exports["solution"]),
        "permitted_axioms": config["permitted_axioms"],
        "unpermitted_axiom_hard_error": False, "num_threads": ns.threads,
        "nat_extension": True, "string_extension": True,
    }, indent=2) + "\n")
    run("nanoda", [lake, "env", "nanoda_bin", str(nanoda_config)])
    if ns.try_con_ron:
        run("con-ron", [lake, "env", "con-ron", str(exports["solution"])], required=False)
    report["required_local_checks_passed"] = True
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    evidence = ROOT / "verification" / config_path.stem
    evidence.mkdir(parents=True, exist_ok=True)
    shutil.copy2(config_path, evidence / "configuration.json")
    shutil.copy2(ROOT / "lean-toolchain", evidence / "lean-toolchain.txt")
    shutil.copy2(out / "report.json", evidence / "report.json")
    for name in ("compare-and-axioms", "lean-kernel", "nanoda", "con-ron"):
        log = out / f"{name}.log"
        if log.exists():
            shutil.copy2(log, evidence / log.name)
    print(f"Local checks passed; full preflight is still required. Report: {out / 'report.json'}")


if __name__ == "__main__":
    main()
