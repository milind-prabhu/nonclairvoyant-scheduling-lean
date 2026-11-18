"""Print Lean's dependency report and reject unexpected axiom dependencies."""
from pathlib import Path
import re
import sys

report = sys.stdin.read()
print(report, end="")
allowed = {"propext", "Classical.choice", "Quot.sound"}
entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", report)
independent = re.findall(r"'([^']+)' does not depend on any axioms", report)
requested = re.findall(r"(?m)^#print axioms (\S+)",
                       (Path(__file__).resolve().parent.parent / "Audit.lean").read_text())
reported = {name for name, _ in entries} | set(independent)
missing = set(requested) - reported
if missing:
    raise SystemExit("Missing axiom reports: " + ", ".join(sorted(missing)))
for name, dependencies in entries:
    unexpected = {x.strip() for x in dependencies.split(",") if x.strip()} - allowed
    if unexpected:
        raise SystemExit(f"Unexpected axioms for {name}: {', '.join(sorted(unexpected))}")
print(f"Axiom check passed: {len(requested)} declarations; only standard Lean axioms.")
