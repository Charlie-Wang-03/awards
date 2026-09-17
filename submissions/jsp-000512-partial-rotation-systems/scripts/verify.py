#!/usr/bin/env python3
"""Build and audit this limited-scope formalization; not a prize-eligibility check."""
from pathlib import Path
import hashlib
import re
import subprocess

root = Path(__file__).resolve().parents[1]
for line in (root / "evidence/SOURCE-SHA256SUMS").read_text().splitlines():
    digest, name = line.split("  ", 1)
    if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
        raise SystemExit(f"Source hash mismatch: {name}")
for source in [root / "Probe.lean", *sorted((root / "Probe").glob("*.lean"))]:
    if re.search(r"\b(sorry|admit|axiom|native_decide)\b", source.read_text()):
        raise SystemExit(f"Disallowed proof placeholder/axiom/native decision token: {source.name}")
subprocess.run(["lake", "build"], cwd=root, check=True)
audit = subprocess.run(["lake", "env", "lean", "Probe/FoundationAudit.lean"],
                       cwd=root, check=True, text=True, capture_output=True)
print(audit.stdout, end="")
print(audit.stderr, end="")
expected = re.findall(r"^#print axioms (\S+)", (root / "Probe/FoundationAudit.lean").read_text(), re.M)
found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit.stdout)
if len(found) != len(expected) or {name for name, _ in found} != set(expected):
    raise SystemExit("Missing or unexpected axiom-audit declarations")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axiom_list in found:
    actual = {a.strip() for a in axiom_list.split(",") if a.strip()}
    if not actual <= allowed:
        raise SystemExit(f"Unexpected axioms for {name}: {actual - allowed}")
print(f"PASS: source integrity, full build, and {len(found)} named axiom audits.")
