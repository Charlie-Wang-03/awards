#!/usr/bin/env python3
"""Build and audit the stated formalization; not a prize-eligibility check."""
from pathlib import Path
import hashlib
import re
import subprocess

root = Path(__file__).resolve().parents[1]
sources = [root / "Probe.lean", *sorted((root / "Probe").glob("*.lean"))]
manifest = {}
for line in (root / "evidence/SOURCE-SHA256SUMS").read_text().splitlines():
    digest, name = line.split("  ", 1)
    if name in manifest:
        raise SystemExit(f"Duplicate source hash: {name}")
    manifest[name] = digest
    if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
        raise SystemExit(f"Source hash mismatch: {name}")
required = {str(p.relative_to(root)) for p in sources} | {
    "lean-toolchain", "lakefile.toml", "lake-manifest.json", "scripts/verify.py"
}
if set(manifest) != required:
    raise SystemExit("Source manifest does not cover the exact proof inputs")
for source in sources:
    if re.search(r"\b(sorry|admit|axiom|native_decide)\b", source.read_text()):
        raise SystemExit(f"Disallowed proof placeholder/axiom/native decision token: {source.name}")
# Require every supplied module to be reachable from the root build target.
reachable = set()
def visit(path):
    if path in reachable:
        return
    reachable.add(path)
    for name in re.findall(r"^import (Probe\.\w+)", path.read_text(), re.M):
        visit(root / (name.replace(".", "/") + ".lean"))
visit(root / "Probe.lean")
if reachable != set(sources):
    raise SystemExit("Root build target does not cover every supplied module")
subprocess.run(["lake", "build"], cwd=root, check=True)
allowed = {"propext", "Classical.choice", "Quot.sound"}
total = 0
for path in sorted((root / "Probe").glob("*Audit.lean")):
    audit = subprocess.run(["lake", "env", "lean", str(path.relative_to(root))],
                           cwd=root, check=True, text=True, capture_output=True)
    print(audit.stdout, end="")
    print(audit.stderr, end="")
    if re.search(r"\b(?:warning|error):", audit.stdout + audit.stderr):
        raise SystemExit(f"Audit emitted a diagnostic: {path.name}")
    expected = re.findall(r"^#print axioms (\S+)", path.read_text(), re.M)
    found = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit.stdout)
    found += [(name, "") for name in re.findall(
        r"'([^']+)' does not depend on any axioms", audit.stdout)]
    if len(found) != len(expected) or {name for name, _ in found} != set(expected):
        raise SystemExit(f"Missing or unexpected axiom-audit declarations: {path.name}")
    for name, axiom_list in found:
        actual = {a.strip() for a in axiom_list.split(",") if a.strip()}
        if not actual <= allowed:
            raise SystemExit(f"Unexpected axioms for {name}: {actual - allowed}")
    total += len(found)
print(f"PASS: source integrity, full build of {len(sources)} modules, and {total} named axiom audits.")
