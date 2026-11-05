# Small odd-phase threshold verification

2026-11-05. This source follows safely pushed research checkpoint
`9e725b7039182a1a8ad5992fd34bd64f0eecbad1`. It proves the original lower bounds
for every 3 <= N <= 20. General family B for n >= 4 remains open.

- `lake build JSP000404Research.OriginalSmallCases`: exit 0, 3,261 jobs.
- `lake env lean verification/small-odd-thresholds-20261105/Audit.lean`:
  exit 0, **53 research modules / 940 declarations / zero failures**.
  The collector includes private declarations and follows all transitive
  dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- `lake env lean JSP000404Research.lean`: exit 0, empty output, after the
  new original-small-cases import was added.
- All ten pinned dependency revisions and their tracked trees pass the
  check in `dependencies.json`. Lean is 4.34.0; Mathlib is
  `5ed2965256430c3649e86755f9576b54eca72435`.

The finite covering theorems use ordinary Lean `decide`, with kernel-checked
proof terms. No external SAT answer or numerical output is a proof premise.
`seven_slot_coverage` covers every partial row, including nonmaximal rows.
The new sources contain no `sorry`, `admit`, `native_decide`, or new axiom.
The separate historical admitted WIP remains outside this imported closure.

`../../SMALL_ODD_THRESHOLD_PROOF.md` gives the written argument and exact
scope. All-N epsilon sharpness keeps its previously recorded attribution.
The initial user checkpoint `e2168310` remains an ancestor; no history has
been rewritten. This is a research checkpoint, with no upstream award write.

Committed logs normalize text to UTF-8 / LF and trim trailing diagnostic
whitespace. Raw logs are preserved in `artifacts/`. Canonical source and
evidence hashes, together with raw-stream hashes, are in `source-sha256.json`.
The historical full-root audit is not presented as an audit of this source.

Run the three commands above from this research project directory with the
pinned toolchain, dependency checkouts, and existing Lake cache.
