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
  The five further whole-cube repairs now pass the canonical outward-order
  target together (3,742 jobs, exit 0); all six printed theorems use only
  the standard three axioms. The complete target log and source hashes are
  identified in `verification/windows-20261105/whole-cube-success-excerpt.log`.
  No assumptions or admissions were added.
- **First full replay finished, exit 1:** `scripts/replay_research_windows.ps1 -Threads 2 -SkipCache`.
  Logs: `artifacts/replay-20261104-195532/`; driver:
  `artifacts/restore-20261105/full-replay-driver.log`.
  It builds the umbrella, the separate admitted root, the repaired bridges,
  and the all-N upper theorem, then runs the strict sorry audit.
  The first umbrella pass has finished with exit 1 on
  `SupportTwoIndexedCertificate` and `ResidualWholeCubeSecondCoordinateCollision`.
  Both source repairs pass direct Lean checks; a fresh umbrella rebuild is
  still required. The separate WIP root passed (3,853 jobs), but its actual
  printed axioms include `sorryAx`. Its subsequent module-wide audit checked
  451 modules / 4,238 declarations and rejected exactly that admitted theorem.
  Root is NOT yet PASS. Earlier root attempts were interrupted after memory
  failures / to repair concrete compiler errors. Process-local two-thread
  execution preserves the user's other processes and system settings.
  `SupportTwoIndexedCertificate` now reuses the identical `ZeroCarry`
  definition of `positiveIndexSet`; that repair awaits an umbrella rebuild.
  A separate real import probe also found a `criticalBadWidth` definition
  collision between `CriticalUnitQuotient` and `CriticalBadMass`. The latter
  now reuses the genuine endpoint definition and its proved formula; its
  angle-excess consumer was adapted without changing any theorem statement.
  A second import probe found differently ordered, same-name list helpers
  in the two projective cut-rotation modules. The helpers in
  `ProjectiveCutRotation` now have distinct names, and their one external
  call is updated; their statements and proofs are unchanged. This choice
  affects 47 umbrella modules rather than 118 for renaming the gap-cut
  variants. The remaining
  suspected duplicate theorems passed a joint import probe. These repairs
  still await a completed rebuild.
  The actual build log also reveals native-decision axiom dependencies in
  historical finite arithmetic certificates. All 29 such tactic calls in
  the umbrella closure have been changed to kernel-checked `decide`, with
  statements unchanged. Direct `lake env lean` checks of all seven source
  files pass, and their printed theorems use only the standard three axioms;
  complete logs/source hashes are retained in verification. The cached
  modules and their dependents still require a full rebuild. This strengthens
  checking of those tables, not the missing geometry.
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
  The same integer witness now also passes the stronger cosine inequality
  needed at upper-strip t=15/4. A complete five-point binary-family argument
  excludes this unchanged-subset recursion for every 3<t<4.
  This extension is reproducible at `50197263d4aac8fd4620c2c7c7955b667cadc444`.
  A further sixteen-point construction now excludes every t>4, so starting
  the same induction above the small cases does not repair it. Explicit
  algebraic coordinates work in both n=4 strips. The written geometric
  proof uses a uniform angular-error bound; an integer check verifies all
  65,536 colourings against 272 designated triples. The isolated t=4 is
  not addressed. The extension is reproducible at
  `80e47652f35c047547e285fb8187d3d033bc81b8`. It does not exclude recursion
  restricted to hypothetical minimal overweight configurations. This is
  not a Lean theorem or an original-problem solution.
- [Six integer points](FULL_BAND_PHASE_COUNTEREXAMPLE.md) now refute the
  proposed at-most-one-full common-phase premise in the genuine lower strip
  `t=349/100`. Exact rational interval arithmetic verifies all 60 angles,
  all 60 event cells, and the endpoint convention: every phase has 2..4
  full vertices. The original cardinality bound remains respected.
  This certificate is written/executable mathematics, not a Lean theorem.
  A second integer witness also has full four-bit completion mass 8..10
  at every phase, refuting the weaker universal target `M>=2*|S|-1=11`.
  Both are reproducible at `92e5a2ada0dffbeb319430f2c072a28c38eae4ed`.
- The historical four-point compensated-deletion witness has also been
  checked exactly at `t=17/5`: 12 strict angle checks and every root/child
  quotient floor pass; mass 7 becomes 6 after each deletion. See Section 7
  of [the audit](COMPENSATED_DELETION_HARD_STOP_2026-09-20.md). Since 7<8,
  this excludes unconditional deletion, not deletion restricted to a
  hypothetical minimal overweight configuration. No Lean geometry claim.
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

Next: replay from a clean committed checkpoint and repair actual errors without
removing imports. Do not edit sources during that replay. The updated script
checks all ten dependency checkout SHAs/clean tracked trees and the source
HEAD/clean tree at both endpoints. Its dependency-checking function has passed
an actual probe; the end-to-end updated replay is still pending.
The prepared `scripts/write_axiom_audits.py` generates module-based transitive
axiom audits for the umbrella and admitted root separately. A real probe on
the already-built upper closure passed: 16 defining modules, 411 declarations,
including private declarations, no axioms beyond the standard three. The
umbrella audit has NOT yet run. The admitted-root audit ran and correctly
rejected `sorryAx`; its raw log hash and exact counts are in verification.
Then pursue the original unweighted thresholds directly, or prove genuine
global non-reusing payment. Both the at-most-one-full phase premise and the
universal completion-mass lower bound `M>=2*|S|-1` are now excluded. A proof
using minimal overweight geometry would need new geometric structure; none
is assumed. The wide-wrap bipartite-phase route also remains UNPROVED;
its latest numerical search found no counterexample, which proves nothing.
No upstream complete-proof PR, prize claim, or eligibility change is authorized
by the current incomplete evidence.
