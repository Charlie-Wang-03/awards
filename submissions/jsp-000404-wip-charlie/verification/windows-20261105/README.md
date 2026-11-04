# Local Windows evidence, 2026-11-05

This directory records a focused compiler repair, not a complete proof of
JSP-000404. The general geometric payment and the final all-N theorem remain
unproved. The original admitted theorem still contains `sorry`.

Source commit: `ac8a70e12193092ac04221999c5bcd5c4a9ea2b6` on
`codex/jsp-000404-goal-20261105` in Charlie-Wang-03/awards.

Run from `submissions/jsp-000404-wip-charlie/` in Windows PowerShell:

```powershell
$env:LEAN_NUM_THREADS = '2'
lake exe cache get
lake build JSP000404Research.ProjectionOrderCanonicalOrder
```

Lean is `leanprover/lean4:v4.34.0`; Mathlib is
`5ed2965256430c3649e86755f9576b54eca72435`. The successful build exits 0
after 3,213 jobs. Its four printed declarations have exactly
`[propext, Classical.choice, Quot.sound]` as their axiom sets.

`projection-order-success.log` contains the captured build output with the
recorded process exit code appended. Only line endings (UTF-8/LF) and trailing
whitespace were normalized for Git; no messages were removed. SHA-256:

    89021ae4338166b07055a7b9641cd7a7db57f77ffce5c4fa7cb3487222cd4570

The original raw capture remains at
`artifacts/restore-20261105/projection-order-build-fixed2.log`, SHA-256
`47a6db6eb67847a152268ec8c90f9a6791fe961a622a747d5e8bd6c62ef2d003`.

The source file `JSP000404Research/ProjectionOrderCanonicalOrder.lean`
has SHA-256:

    6fcbd2e209d353a973efb0e908a48befc6e08f23a4e506cd73c74336f7998eb2

These hashes cover this focused result only. They do not certify later
working-tree repairs or other modules.

For the broader outstanding research checks, use
`scripts/replay_research_windows.ps1`. It builds the umbrella, the separate
admitted module, and the projection-order dependents, then runs the strict
sorry audit. The script always labels its output INCOMPLETE because a final
original-problem theorem has not been supplied. Its output is placed in
ignored `artifacts/` directories. The strict audit currently must fail on
the known global-payment admission; accepting that failure as proof is invalid.

The first full-root attempt produced file-read errors while Windows reported
insufficient memory. The two-thread attempt was interrupted to repair the
canonical-order bridge. Neither attempt is a root PASS. Their full raw logs,
and the intermediate failed focused attempts, remain in ignored
`artifacts/restore-20261105/`.
