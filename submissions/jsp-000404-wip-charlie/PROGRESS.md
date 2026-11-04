# JSP-000404 progress

Status: **INCOMPLETE — goal active; the full original problem is not proved.**
Updated: 2026-11-05 (Asia/Shanghai).

- Workspace: `D:\awards`; branch `codex/jsp-000404-goal-20261105`.
  Baseline: `d7e5c780362d09057102c651427fc1203b9165f2` (connector repair).
  Upstream rules inspected at `f8801a856529dce27e738c6b305e46d76e7c387c`.
  Main and all pre-existing research branches are preserved.
- Pins: Lean `v4.34.0`; Mathlib
  `5ed2965256430c3649e86755f9576b54eca72435`.
  The complete Lake manifest is tracked. Official Windows toolchain archive
  hash and restoration evidence are retained in the earlier checkpoint.
  `lake exe cache get` passes: exit 0, 8,908 files.
- **Last verified original-problem component:**
  `3acbdd0ad52bebb3dd43dd86d380bf04a6eeb984`.
  `lake build JSP000404Research.OriginalUpperBound` passes (3,243 jobs).
  `original_sharpness_allN` proves ordinary-point epsilon sharpness for
  every N >= 3. Three further theorems identify the injective Fin N,
  finite-set, and genuine geometric-extremum formulations. All four
  print only `propext`, `Classical.choice`, `Quot.sound`.
  `OriginalProblem` is a precise proposition, **not a proved theorem**.
- This closes the sharpness branch and statement-correspondence branch of
  [PROOF_DAG.md](PROOF_DAG.md). It uses attributed prior constructions,
  not a new priority claim. [Written proof](SHARPNESS_CONSTRUCTIONS.md);
  [source attribution](EXTERNAL_PROOF_ATTRIBUTION.md).
  The external dependency is `aznikline/jsp-000404-lean` at
  `cbfbbef188f5f98eead6045d7c3548de3c1b701a`.
  Its 13-module upper closure excludes the conditional lower theorem.
  All 14 vendored source/license Git-blob hashes match its upstream manifest.
  No third-party source code or PDFs are vendored into this repository.
- Verified compiler repairs:
  `ac8a70e12193092ac04221999c5bcd5c4a9ea2b6` fixes the genuine projection order;
  `51db72e85ec50fc7cbd4bde998b5ab518385fff0` fixes both canonical QTT wrappers.
  Their builds pass (3,213 / 3,447 jobs), with only the standard three axioms.
  `b678ab677969688ef3837aea8fcf9004d45a5b79` fixes six collision/whole-cube
  dependencies that compiled successfully during downstream failing attempts.
  The canonical whole-cube wrapper and augmenting-terminal repair still await the
  complete whole-cube target result. No assumptions or admissions were added.
- **Full replay now running:** `scripts/replay_research_windows.ps1 -Threads 2 -SkipCache`.
  Logs: `artifacts/replay-20261104-195532/`; driver:
  `artifacts/restore-20261105/full-replay-driver.log`.
  It builds the umbrella, the separate admitted root, the repaired bridges,
  and the all-N upper theorem, then runs the strict sorry audit.
  Root is NOT yet PASS. Earlier root attempts were interrupted after memory
  failures / to repair concrete compiler errors. Process-local two-thread
  execution preserves the user's other processes and system settings.
- Current import inventory: 1,686 local modules including the umbrella;
  995 in its revised closure, 691 outside. The admitted root is outside it;
  its separate closure has 451 modules, 60 absent from the umbrella closure.
  A successful umbrella alone would therefore not certify the admitted root.
- Strict lexical audit: 1 executable `sorry`, at
  `PlanarLowerBranchProofAdmittedWIP.lean:935`; audit exits 1.
  The mathematical gap is broader: unrestricted lower-strip payment,
  upper-strip weighted capacity, and the unconditional all-N lower bound.
  The exact remaining payment and two sufficient unweighted threshold
  families are recorded in [PROOF_DAG.md](PROOF_DAG.md).
- Excluded routes, with complete written counterexamples:
  [four-centre / perfect-GC witness](UPPER_FOUR_CENTRE_COUNTEREXAMPLE.md)
  has mass ten at n=3, delta=3/4 and refutes the printed strengthened maximum
  nine. It preserves the original capacity ten. An odd-n family extends it.
  [five integer points](WIDTH_DROP_PARTITION_COUNTEREXAMPLE.md) refute
  unchanged-subset binary width-drop recursion at t=10/3. The integer
  checker passes ten triples and 32 colourings. Neither is Lean-certified.
- [Six integer points](FULL_BAND_PHASE_COUNTEREXAMPLE.md) now refute the
  proposed at-most-one-full common-phase premise in the genuine lower strip
  `t=349/100`. Exact rational interval arithmetic verifies all 60 angles,
  all 60 event cells, and the endpoint convention: every phase has 2..4
  full vertices. The original cardinality bound remains respected.
  This certificate is written/executable mathematics, not a Lean theorem.
- Sendov Acta pp. 39–40 and 42 were independently inspected as images.
  Arbitrary-s induction remains missing; numerator 2 and epsilon inversion
  are required. Public #5131 takes `GeometricCertificates` for general lower
  bounds; #100/#647 claim finite certificates through N=16. Their finite
  lower results have not been locally replayed and do not close all N.
- Historical CI: focused connector run
  [40653990253](https://github.com/Charlie-Wang-03/awards/actions/runs/40653990253)
  passes. Admitted-root run
  [40330564100](https://github.com/Charlie-Wang-03/awards/actions/runs/40330564100)
  explicitly prints `sorryAx`; its green build is not a proof.
  New reproducible logs/hashes are in [verification](verification/windows-20261105/README.md).

Next: finish the full replay and repair actual errors without removing imports.
Then pursue the original unweighted thresholds directly, or prove genuine
global non-reusing payment. The at-most-one-full phase route is now excluded.
A phase criterion retaining the entire Hansel completion mass is weaker and
still UNPROVED; it must first survive adversarial testing. Numerical
falsification attempts alone establish no theorem.
No upstream complete-proof PR, prize claim, or eligibility change is authorized
by the current incomplete evidence.
