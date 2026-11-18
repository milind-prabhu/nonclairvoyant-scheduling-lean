"""Check that this development contains no admitted proof or custom axiom."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
paths = sorted((root / "Scheduling").glob("*.lean"))
paths += [root / "Scheduling.lean", root / "Audit.lean"]
bad = []
theorems = 0
for path in paths:
    source = path.read_text()
    theorems += len(re.findall(r"(?m)^\s*(?:@\[[^\n]*\]\s*)?theorem\s+", source))
    for pattern in (r"\b(?:sorry|admit|native_decide)\b", r"(?m)^\s*(?:axiom|opaque|unsafe)\s+",
                    r"\[.*\b(?:implemented_by|extern)\b"):
        if re.search(pattern, source):
            bad.append(str(path.relative_to(root)))
if bad:
    raise SystemExit("Unexpected proof hole or unchecked declaration: " + ", ".join(bad))
print(f"Source check passed: {len(paths)} Lean files, {theorems} theorems; no admitted proofs or custom axioms.")
