#!/usr/bin/env python3
"""Audit executable Lean source for the explicit proof holes sorry and admit.

Comments (including nested block comments) and ordinary string literals are
excluded. This is a lexical source audit, not a replacement for Lean's kernel
checking or a theorem's #print axioms report.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

HOLE = re.compile(r"(?<![\w])(?:sorry|admit)(?![\w])")


def executable_source(src: str) -> str:
    """Mask non-code characters while retaining newline offsets."""
    out = list(src)
    n = len(src)
    i = 0

    def blank(a: int, b: int) -> None:
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        if src.startswith("--", i):
            end = src.find("\n", i)
            if end < 0:
                end = n
            blank(i, end)
            i = end
        elif src.startswith("/-", i):
            start = i
            i += 2
            depth = 1
            while i < n and depth:
                if src.startswith("/-", i):
                    depth += 1
                    i += 2
                elif src.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            blank(start, i)
        elif src[i] == '"':
            start = i
            i += 1
            while i < n:
                if src[i] == "\\":
                    i += 2
                elif src[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            blank(start, min(i, n))
        else:
            i += 1
    return "".join(out)


def self_test() -> None:
    cases = [
        ("theorem p : True := by\n  sorry\n", ["sorry"]),
        ("theorem p : True := by admit", ["admit"]),
        ("-- sorry\n/- admit -/\nTrue", []),
        ("/- nested /- sorry -/ admit -/\nTrue", []),
        ('def s := "sorry and admit"', []),
        ("theorem p : True := by\n  trivial -- admit", []),
        ("by\n  exact (sorry)", ["sorry"]),
        ("by\n  exact True.intro", []),
    ]
    for src, expected in cases:
        actual = HOLE.findall(executable_source(src))
        if actual != expected:
            raise AssertionError(f"scanner mismatch: {actual!r} != {expected!r}")
    print(f"scanner self-test: PASS ({len(cases)} cases)")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=Path("JSP000404Research"))
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--allowed-wip", type=Path, default=None,
                    help="Exact single Lean source file allowed provisional sorry tokens")
    ap.add_argument("--wip-max-sorries", type=int, default=0)
    args = ap.parse_args()
    self_test()
    if args.self_test:
        return 0
    files = sorted(args.root.rglob("*.lean"))
    if not files:
        print(f"ERROR: no Lean files found under {args.root}", file=sys.stderr)
        return 2
    failures: list[str] = []
    provisional: list[str] = []
    if args.wip_max_sorries < 0:
        print("ERROR: negative WIP allowance", file=sys.stderr)
        return 2
    if args.wip_max_sorries and args.allowed_wip is None:
        print("ERROR: WIP allowance requires one exact file", file=sys.stderr)
        return 2
    if args.allowed_wip is not None and args.allowed_wip not in files:
        print(f"ERROR: allowed WIP path not found: {args.allowed_wip}", file=sys.stderr)
        return 2
    for file in files:
        src = file.read_text(encoding="utf-8")
        code = executable_source(src)
        for m in HOLE.finditer(code):
            line = code.count("\n", 0, m.start()) + 1
            entry = f"{file}:{line}: explicit {m.group()}"
            if file == args.allowed_wip and m.group() == "sorry":
                provisional.append(entry)
            else:
                failures.append(entry)
    print(f"Lean source files scanned: {len(files)}")
    if len(provisional) > args.wip_max_sorries:
        failures.append(
            f"WIP budget exceeded: {len(provisional)} > {args.wip_max_sorries}"
        )
    if failures:
        print("\n".join(failures))
        print(f"FAILED: {len(failures)} unauthorised holes or audit violations")
        return 1
    if provisional:
        print("PROVISIONAL WIP HOLES (NOT A COMPLETE PROOF):")
        print("\n".join(provisional))
        print("WARNING: the WIP root theorem depends on Lean sorryAx.")
    print("PASS: zero executable sorry/admit outside the exact allowed WIP path")
    return 0


if __name__ == "__main__":
    sys.exit(main())
