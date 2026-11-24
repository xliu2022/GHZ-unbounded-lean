#!/usr/bin/env python3
"""Check the source-layout subset of Palomar's published requirements.

This is a local preparation check, not the registry's source scan, metadata
validation, editorial review, or full preflight. It reads ordinary source files
and the pinned manifest; it neither changes a sandbox nor downloads dependencies.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_SUFFIXES = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}
PERMITTED = {"propext", "Quot.sound", "Classical.choice"}
ALLOWED_CONFIG_KEYS = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms", "definition_names", "enable_nanoda"}
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
REV = re.compile(r"[0-9a-f]{40}\Z")
PUBLIC_GITHUB = re.compile(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?\Z")


def without_comments(text: str) -> str:
    """Remove nested Lean block comments and line comments, preserving newlines."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1; i += 2
            elif text.startswith("-/", i):
                depth -= 1; i += 2
            else:
                if text[i] == "\n": out.append("\n")
                i += 1
        elif text.startswith("/-", i):
            depth = 1; i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            # Preserve strings without treating embedded comment delimiters as comments.
            start = i; i += 1
            while i < len(text):
                if text[i] == "\\": i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
            out.append(text[start:i])
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-metadata", action="store_true")
    args = parser.parse_args()
    failures, warnings = [], []
    config_paths = sorted(ROOT.glob("comparator*.json"))
    challenge_paths = {
        json.loads(p.read_text())["challenge_module"].replace(".", "/") + ".lean"
        for p in config_paths
    }
    challenge_holes = 0
    files = [p for p in ROOT.rglob("*") if p.is_file()
             and not any(part in {".git", ".lake"} for part in p.relative_to(ROOT).parts)]
    regular = [p for p in files if not p.is_symlink()]
    size = sum(p.stat().st_size for p in regular)
    if size > 500 * 1024 * 1024:
        failures.append(f"Source checkout is {size} bytes, above 500 MiB")
    lean_sources = []
    for p in files:
        rel = str(p.relative_to(ROOT))
        if p.suffix in ARTIFACT_SUFFIXES:
            failures.append(f"Compiled artifact outside .lake: {rel}")
        with p.open("rb") as source_stream:
            prefix = source_stream.read(100)
        if prefix.startswith(b"version https://git-lfs.github.com/spec/v1"):
            failures.append(f"Git LFS pointer: {rel}")
        if p.suffix != ".lean":
            continue
        if p.is_symlink():
            failures.append(f"Lean source is a symlink: {rel}")
            continue
        source = p.read_text(encoding="utf-8")
        line_count = len(source.splitlines())
        if line_count > 10000:
            failures.append(f"Lean source has {line_count} physical lines: {rel}")
        code = without_comments(source)
        # This lexical check supplements, and does not replace, the kernel and
        # declaration-closure axiom audits. Ignore ordinary string literals.
        scan = re.sub(r'"(?:\\.|[^"\\])*"', '""', code)
        holes = re.findall(r"\b(?:sorry|admit)\b", scan)
        if rel in challenge_paths:
            challenge_holes += len(holes)
        elif holes:
            failures.append(f"Proof placeholder outside a Challenge: {rel}")
        if re.search(r"\bnative_decide\b|\bLean\.ofReduceBool\b|\bdecide\s*\+\s*native\b", scan):
            failures.append(f"Native reduction proof command: {rel}")
        if re.search(r"^\s*(?:(?:private|public|protected)\s+)*axiom\b", scan, re.M):
            failures.append(f"Project axiom declaration: {rel}")
        if p.name != "lakefile.lean" and not re.match(r"\s*module\b", code):
            failures.append(f"Missing module header: {rel}")
        lean_sources.append({"path": rel, "lines": line_count, "bytes": p.stat().st_size})
    configs = []
    for p in config_paths:
        c = json.loads(p.read_text())
        if set(c) - ALLOWED_CONFIG_KEYS:
            failures.append(f"Unsupported Comparator keys: {p.name}")
        if not c.get("theorem_names"):
            failures.append(f"No selected theorems: {p.name}")
        if not set(c.get("permitted_axioms", [])) <= PERMITTED:
            failures.append(f"Unpermitted axioms: {p.name}")
        for key in ("challenge_module", "solution_module"):
            value = c.get(key, "")
            if not NAME.fullmatch(value):
                failures.append(f"Invalid {key}: {p.name}")
                continue
            source_path = ROOT / (value.replace(".", "/") + ".lean")
            if not source_path.is_file() or source_path.is_symlink():
                failures.append(f"Missing ordinary {key} source: {value}")
            elif key == "challenge_module":
                source = source_path.read_text()
                lines, byte_count = len(source.splitlines()), source_path.stat().st_size
                if lines > 1000 or byte_count > 100 * 1024:
                    failures.append(f"Challenge hard size limit exceeded: {source_path.name}")
                elif lines > 300 or byte_count > 32 * 1024:
                    warnings.append(f"Challenge exceeds advisory size: {source_path.name} ({lines} lines, {byte_count} bytes)")
                imports = re.findall(r"^\s*(?:public\s+)?import\s+([\w.]+)", without_comments(source), re.M)
                for imported in imports:
                    if not imported.startswith(("Mathlib.", "Init", "Lean.", "Std.")):
                        failures.append(f"Project-specific Challenge import: {source_path.name}: {imported}")
        if c.get("challenge_module") == c.get("solution_module"):
            failures.append(f"Challenge and Solution are identical: {p.name}")
        configs.append({"path": p.name, "theorems": c.get("theorem_names", []),
                        "definitions": c.get("definition_names", [])})
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest.get("packages", []):
        if package.get("type") == "git":
            if not REV.fullmatch(package.get("rev", "")):
                failures.append(f"Unpinned dependency: {package.get('name')}")
            if not PUBLIC_GITHUB.fullmatch(package.get("url", "")):
                failures.append(f"Noncanonical public GitHub URL: {package.get('name')}")
    if args.require_metadata and not (ROOT / "formalization.yaml").is_file():
        failures.append("formalization.yaml requires the responsible human's confirmed names")
    report = {"kind": "local-source-preparation-check", "palomar_full_preflight": False,
              "source_bytes": size, "regular_files": len(regular),
              "lean_files": len(lean_sources), "maximum_lean_lines": max(x["lines"] for x in lean_sources),
              "challenge_placeholders": challenge_holes,
              "proof_source_scan": "lexical; supplemented by kernel and axiom-closure checks",
              "configurations": configs, "warnings": warnings, "failures": failures,
              "passed": not failures}
    out = ROOT / "verification/source-layout.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
