#!/usr/bin/env python3
"""Check the output of AxiomAudit.lean against its exact target inventory."""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
targets = (root / "axiom-targets.txt").read_text().splitlines()
output = (root / "axiom-results.txt").read_text().splitlines()
pattern = re.compile(r"^'([^']+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)$")
allowed = {"propext", "Classical.choice", "Quot.sound"}
seen = {}
for line in output:
    match = pattern.fullmatch(line)
    if not match:
        print(f"Unexpected output: {line}", file=sys.stderr)
        sys.exit(1)
    name, axioms = match.groups()
    if name in seen:
        print(f"Duplicate target: {name}", file=sys.stderr)
        sys.exit(1)
    found = set(axioms.split(", ")) if axioms else set()
    if found - allowed:
        print(f"Nonstandard axioms in {name}: {found - allowed}", file=sys.stderr)
        sys.exit(1)
    seen[name] = found
if len(targets) != len(set(targets)) or set(targets) != set(seen):
    print(f"Target mismatch: missing={set(targets) - set(seen)}, extra={set(seen) - set(targets)}", file=sys.stderr)
    sys.exit(1)
print(f"PASS {len(targets)} theorem targets; standard axioms only")
