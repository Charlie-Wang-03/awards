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

The next verified source commit is
`51db72e85ec50fc7cbd4bde998b5ab518385fff0`. It repairs the concrete-order
binders and definition unfolding in the two QTT wrappers. The command

```powershell
lake build JSP000404Research.ResidualQTTTCanonicalOrderRigidity JSP000404Research.ProjectionQTTTCanonicalOrderRigidity
```

completed with exit 0 (3,447 jobs). The two printed declarations in each
target have only `propext`, `Classical.choice`, and `Quot.sound`.
`qttt-order-success.log` retains every message, with only UTF-8/LF line
endings and trailing whitespace normalized. SHA-256:

    2be608b42519e3274390b89aadacbf5f9201140349991c8984c173c1adb37378

The raw capture `artifacts/restore-20261105/qttt-canonical-fixed2.log` has
SHA-256:

    adcc962a7d41fb298f49453d440d4ffd78b2028785a384d47abc67070206cd09

At source commit `3acbdd0ad52bebb3dd43dd86d380bf04a6eeb984`, the command
`lake build JSP000404Research.OriginalUpperBound` passes (3,243 jobs,
exit 0). This proves all-N ordinary epsilon sharpness and exact correspondence
of the injective, finite-set, and geometric-extremum statements. All four
printed local declarations and both printed external upper declarations have
only the standard three axioms. It does not prove the all-N lower bound.

`original-upper-success.log` retains the entire captured output under the
same line-ending/whitespace normalization. SHA-256:

    ca9bc64be3cdeb38056485d66e472bd9bec58c1337c62a8e00f76006b02443ba

Raw `artifacts/restore-20261105/original-upper-bound-first.log` SHA-256:

    2ec52ffacc1b1688ba8724c21eff900b36d904f704951df4a72799764be222e1

The external package is fixed at
`cbfbbef188f5f98eead6045d7c3548de3c1b701a`; its 13-module upper dependency
closure excludes the conditional lower theorem. Attribution and the original
source SHA are recorded in `EXTERNAL_PROOF_ATTRIBUTION.md`.

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

## Module-based transitive axiom collector

`scripts/write_axiom_audits.py` generates separate standalone Lean commands
for the umbrella and admitted root. It enumerates declarations by their
defining module, including private declarations; each declaration is checked
with Lean 4.34.0's `Lean.collectAxioms`, the collector used by `#print axioms`.
Every dependency outside `{propext, Classical.choice, Quot.sound}` causes an
error. An unavailable declaration or an empty audit also causes an error.
This audit does not establish that a theorem's hypotheses are discharged.

The collector has been executed on the already-built
`JSP000404Research.OriginalUpperBound` closure, without starting a second
Lake build. The actual command was:

```powershell
$env:LEAN_NUM_THREADS = '1'
lake env lean artifacts/restore-20261105/axiom-audits/CollectorProbe.lean
```

The probe is the generated `RootAxiomAudit.lean` with only its first import
changed to `JSP000404Research.OriginalUpperBound`. It inspected 16 defining
modules and 411 declarations, including the 13 external upper modules,
`SharpCentre`, `OriginalProblemStatement`, and `OriginalUpperBound`.
There were zero unexpected axiom dependencies; the process exited 0.
The four local statement/sharpness theorems are unchanged from verified
source commit `3acbdd0ad52bebb3dd43dd86d380bf04a6eeb984`.

`collector-probe-success.log` contains every output line, with only UTF-8/LF
line endings normalized. SHA-256:

    6e14cef7cf8e0061dec9406ef57612e0f1c8f6baf5aec9d80dded190303ebd01

Raw `artifacts/restore-20261105/axiom-audits/collector-probe.log` SHA-256:

    7f7ed78051f8039f4d79eb70ee8faa498adff7e5485d52ff3993ede608239c12

The exact generated `CollectorProbe.lean` SHA-256:

    d5f4a0a659dc8dd6abdff4d7108bb4cc192eae720f08cf31566e91e220e79677

The umbrella and admitted-root audits have not yet been executed. The probe
is evidence for the upper closure and collector only, not a full-root PASS.
The replay script now runs these two audits after the builds. A root whose
build failed in that same replay is explicitly skipped and counted as a
failed check, so a stale olean cannot produce a misleading audit PASS.
The already-running `replay-20261104-195532` process uses the earlier script;
the new audit steps apply to the next replay.

## Kernel-checked finite arithmetic tables

The full replay exposed generated `._native.native_decide.ax_...` dependencies
in historical arithmetic certificates. All 29 `native_decide` calls in the
umbrella closure were replaced by `decide` in these seven modules, without
changing any theorem statement:

- `AggregateSplitExistenceHardStop`
- `AggregateSplitHardStopResolution`
- `BalancedBinarySplitHardStop`
- `BinaryKraftTree`
- `BinarySplitHardStopResolution`
- `CompensatedDeletionHardStop`
- `StableCounterexampleData`

Each source was checked with `LEAN_NUM_THREADS=1` and
`lake env lean JSP000404Research/<module>.lean`, without emitting an olean.
All seven commands exited 0; the printed theorems use only a subset of
`propext`, `Classical.choice`, and `Quot.sound`. The complete outputs, each
source SHA-256, and each raw log SHA-256 are in `kernel-decide-success.log`.
UTF-8/LF line endings and trailing whitespace were normalized when concatenating the outputs.
The combined log SHA-256 is:

    da830f9a3966a9f774a42aad636dfb648cb4c6c4cccca8ca3eeb517019057486

These checks establish the finite arithmetic propositions, not their
geometric realizations or the missing global payment. They also do not
replace a fresh umbrella build and its module-wide axiom audit: the old
oleans were deliberately left untouched by these direct checks.
