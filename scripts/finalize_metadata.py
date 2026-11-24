#!/usr/bin/env python3
"""Fill the prepared metadata with explicitly supplied human identities.

The template and output use JSON syntax, which is also valid YAML. This
script does not publish, commit, submit, or infer a person's identity.
"""
import argparse
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--author", action="append", required=True)
parser.add_argument("--maintainer", action="append", required=True)
args = parser.parse_args()
authors = [name.strip() for name in args.author]
maintainers = [name.strip() for name in args.maintainer]
if any(not name for name in authors + maintainers):
    parser.error("Names must be nonempty and identify the responsible humans")
record = json.loads((root / "formalization.yaml.in").read_text())
record["project"]["authors"] = list(dict.fromkeys(authors))
record["project"]["responsible_maintainers"] = list(dict.fromkeys(maintainers))
destination = root / "formalization.yaml"
destination.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n")
print(f"Prepared {destination}; review it before committing or submitting.")
