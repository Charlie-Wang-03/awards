#!/usr/bin/env python3
"""Source-aware, fail-closed Lake artifact reuse for fast JSP-000404 checks.

Fast CI certifies only its selected Lean targets, not the complete conjecture.
A cached .olean may be reused only when the Lean source and every transitive
project-local import have the same content as the cached successful build.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
SOURCES = PROJECT / "JSP000404Research"
BUILD = PROJECT / ".lake" / "build"
INDEX = BUILD / ".jsp000404_source_index.json"
PREFIX = "JSP000404Research."
VERSION = 1


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_paths():
    result = {p.relative_to(PROJECT).as_posix(): p for p in SOURCES.rglob("*.lean")}
    root = PROJECT / "JSP000404Research.lean"
    if root.exists():
        result[root.name] = root
    return result


def module_name(path):
    if path == "JSP000404Research.lean":
        return "JSP000404Research"
    start = "JSP000404Research/"
    if path.startswith(start) and path.endswith(".lean"):
        return path[:-5].replace("/", ".")
    return None


def reverse_graph(paths):
    reversed_imports = {}
    import_line = re.compile(r"^\s*import\s+(.+?)(?:\s*--.*)?$")
    for path, src in paths.items():
        owner = module_name(path)
        for line in src.read_text(encoding="utf-8").splitlines():
            match = import_line.match(line)
            if not match:
                continue
            for dependency in match.group(1).split():
                if dependency == "JSP000404Research" or dependency.startswith(PREFIX):
                    reversed_imports.setdefault(dependency, set()).add(owner)
    return reversed_imports


def invalidation_closure(changed, paths):
    graph = reverse_graph(paths)
    affected = set(changed)
    pending = list(changed)
    while pending:
        for dependent in graph.get(pending.pop(), ()):
            if dependent not in affected:
                affected.add(dependent)
                pending.append(dependent)
    return affected


def purge_artifacts(affected):
    if not BUILD.exists() or not affected:
        return 0
    removed = 0
    for path in BUILD.rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(BUILD).parts
        if "JSP000404Research" in relative:
            i = relative.index("JSP000404Research")
            tail = list(relative[i + 1 :])
            if not tail:
                continue
            # Files have extensions such as .olean, .ilean, .trace, .c, .o.
            module = PREFIX + ".".join(tail[:-1] + [tail[-1].split(".")[0]])
        elif path.name.startswith("JSP000404Research."):
            module = "JSP000404Research"
        else:
            continue
        if module in affected:
            path.unlink()
            removed += 1
    return removed


def event_changed():
    if os.environ.get("GITHUB_EVENT_NAME") != "push":
        return [], False
    before = os.environ.get("GITHUB_EVENT_BEFORE", "")
    after = os.environ.get("GITHUB_SHA", "")
    if not re.fullmatch(r"[0-9a-f]{40}", before) or set(before) == {"0"}:
        return [], True
    if not re.fullmatch(r"[0-9a-f]{40}", after):
        return [], True
    check = subprocess.run(["git", "cat-file", "-e", before + "^{commit}"],
                           cwd=PROJECT, capture_output=True)
    if check.returncode:
        subprocess.run(["git", "fetch", "--no-tags", "--depth=1", "origin", before],
                       cwd=PROJECT, check=False, capture_output=True)
    diff = subprocess.run(["git", "diff", "--name-only", before, after, "--"],
                          cwd=PROJECT, text=True, capture_output=True)
    if diff.returncode:
        return [], True
    prefix = PROJECT.relative_to(PROJECT.parents[1]).as_posix() + "/"
    return [p[len(prefix):] for p in diff.stdout.splitlines()
            if p.startswith(prefix)], False


def prepare():
    files = source_paths()
    hashes = {name: sha256(src) for name, src in files.items()}
    previous = None
    if INDEX.exists():
        try:
            record = json.loads(INDEX.read_text(encoding="utf-8"))
            if record.get("version") == VERSION and isinstance(record.get("sources"), dict):
                previous = record["sources"]
        except (ValueError, OSError):
            pass

    if previous is None and BUILD.exists():
        # Never trust a build directory whose source provenance is unknown.
        shutil.rmtree(BUILD)
        BUILD.mkdir(parents=True, exist_ok=True)
    modified = set()
    if previous is not None:
        modified.update(module_name(p) for p in previous.keys() | hashes.keys()
                        if previous.get(p) != hashes.get(p))
    changed_files, uncertain = event_changed()
    modified.update(module_name(p) for p in changed_files if module_name(p))
    modified.discard(None)
    invalidate = invalidation_closure(modified, files)
    removed = purge_artifacts(invalidate)

    if os.environ.get("GITHUB_EVENT_NAME") == "workflow_dispatch":
        supplied = os.environ.get("INPUT_MODULES", "").strip()
        requested = [token.strip() for token in re.split(r"[\s,]+", supplied) if token.strip()]
        if not requested:
            raise SystemExit("Manual fast CI requires module names (use full workflow for complete verification).")
        targets = []
        for token in requested:
            name = token if token == "JSP000404Research" or token.startswith(PREFIX) else PREFIX + token
            if name != "JSP000404Research" and not re.fullmatch(
                    r"JSP000404Research(?:\.[A-Za-z0-9_]+)+", name):
                raise SystemExit("Invalid module: " + token)
            if name != "JSP000404Research" and \
                    name.replace(".", "/") + ".lean" not in files:
                raise SystemExit("Module not found: " + name)
            targets.append(name)
    else:
        if uncertain or any(p in {"lakefile.toml", "lean-toolchain", "lake-manifest.json"}
                            for p in changed_files):
            targets = ["JSP000404Research"]
        else:
            targets = sorted(m for m in modified if m in
                             {module_name(p) for p in files})
            # A CI/script-only push exercises a small known-good kernel target.
            if not targets and any(p in {
                    "scripts/jsp000404_incremental_ci.py",
                    "scripts/jsp000404_sorry_audit.py"} for p in changed_files):
                targets = ["JSP000404Research.BooleanFlipCore"]
    targets = sorted(set(targets))
    print("Previously cached source index:", "present" if previous is not None else "absent")
    print("Invalidated project modules:", len(invalidate))
    print("Removed stale build artifacts:", removed)
    print("Fast-mode Lean targets:", ", ".join(targets) if targets else "(none)")
    with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as stream:
        stream.write("targets=" + " ".join(targets) + "\n")


def snapshot():
    BUILD.mkdir(parents=True, exist_ok=True)
    current = {name: sha256(src) for name, src in source_paths().items()}
    INDEX.write_text(json.dumps({"version": VERSION, "sources": current},
                                sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print("Recorded successful source snapshot:", len(current), "Lean files")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["prepare", "snapshot"])
    arguments = parser.parse_args()
    if arguments.command == "prepare":
        prepare()
    else:
        snapshot()
