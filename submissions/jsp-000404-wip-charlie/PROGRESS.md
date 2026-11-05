# JSP-000404 progress

**INCOMPLETE — blocked on the unconditional all-N geometric lower bound.**
2026-11-05, Windows. No complete original-problem theorem or prize submission.

**Last reproducible research source:** `b24bf60107959020e7b29b6e1263b739509987b0`
on `Charlie-Wang-03/awards:codex/jsp-000404-goal-20261105`. Baseline:
`d7e5c780362d09057102c651427fc1203b9165f2`. Upstream rules were inspected
at `f8801a856529dce27e738c6b305e46d76e7c387c`; main and earlier research
branches are preserved. The evidence commit following the checked source
contains reports, complete audit outputs and an independent Python checker.

## What actually passed

- Lean `v4.34.0`; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
  Cache restoration passed (8,908 files). The full replay started and ended
  at the same clean source commit. All ten dependency checkout SHAs and
  tracked trees passed both endpoint checks. This used the local Lake cache.
- All seven targets built: the umbrella (9,933 jobs), separate admitted
  WIP (3,853), four canonical-order targets, and `OriginalUpperBound` (3,243).
  Projection/instance binders, whole-cube equalities, import collisions and
  finite arithmetic certificate checks were repaired without dropping imports.
- Umbrella axiom audit: **1,008 modules / 10,619 declarations / 0 failures**.
  Separate WIP audit: **451 / 4,238 / 1 failure**. Precisely
  `ProjectionOrdered.planar_lower_branch_dyadic_capacity_admitted_wip`
  depends on `sorryAx`. The strict scanner finds one executable `sorry` at
  `PlanarLowerBranchProofAdmittedWIP.lean:935`. Replay exit **1** is correct.
  The umbrella does not import the admitted root; 691 local modules are
  outside the umbrella. No whole-source-tree or original-theorem PASS is inferred.

[Full verification and reproducible commands](verification/windows-20261105/README.md).
From this project directory: `.\scripts\replay_research_windows.ps1 -Threads 2 -SkipCache`
after `lake exe cache get`. The raw run is `artifacts/replay-20261104-222505/`.

## Mathematical status

The original statement quantifies over injective enumerations of N ordinary
planar points, N >= 3. It uses the unoriented angle at the middle of three
pairwise distinct points.
`original_sharpness_allN` proves the epsilon-sharpness half for every such N.
The statement correspondences to finite sets and the actual geometric
extremum are also proved. This branch of the DAG first passed at
`3acbdd0ad52bebb3dd43dd86d380bf04a6eeb984` and passed again in the full
replay. [Written proof](SHARPNESS_CONSTRUCTIONS.md);
[attribution](EXTERNAL_PROOF_ATTRIBUTION.md). The construction is prior work:
superpilot69/ChatGPT 6 Astra, with aznikline's all-N packaging pinned at
`cbfbbef188f5f98eead6045d7c3548de3c1b701a`.

**Remaining root obligation:** `∀ N, 3 ≤ N → OriginalLowerBound N`.
For n >= 2, the two exact unweighted threshold families still needed in
general say that strict caps at (1-2/(2n+1))*pi and (1-1/(n+1))*pi imply,
respectively, cardinalities <= 2^n and <= 5*2^(n-2). The source's
arbitrary-centre induction does not derive these inequalities. The current
lower-strip route needs an actual retained-active choice whose covered
blockers, duplicate losses and other terminal/twin debt are paid **jointly**
by exterior true holes and unreserved dyadic surplus, without reuse.
The upper-strip global capacity also lacks an unconditional proof.
[Exact premises, alternatives and sources](PROOF_DAG.md).

## Excluded routes and resumption condition

- [Four-centre witness](UPPER_FOUR_CENTRE_COUNTEREXAMPLE.md): mass 10 violates
  the printed strengthened maximum 9, but respects the original cap 10.
- [Fixed-t deletion](COMPENSATED_DELETION_HARD_STOP_2026-09-20.md) and
  [unchanged-subset recursion](WIDTH_DROP_PARTITION_COUNTEREXAMPLE.md) fail
  without extra hypotheses. The latter has a written realization for every
  3<t<4 and every t>4; the 16-word checker covers 65,536 colourings. Neither
  witness excludes a reduction proved only for a hypothetical minimal
  overweight configuration. These geometric counterexamples are not Lean theorems.
- [Phase certificates](FULL_BAND_PHASE_COUNTEREXAMPLE.md) exclude the
  one-full-vertex and completion-mass shortcuts. An independent rational
  recheck of a [published 21-row arc model](https://github.com/jerrylijize1224-star/jsp404-lean-partial/tree/09b2ee9cab2da6ca977f682f1c8359b5e90d13d0)
  excludes an upper-strip argument based only on row diameter and pairwise
  antipodal compatibility: every pair passes, but one triple is nonrealizable.
  Its reported exact finite values are credited to that project and were
  not kernel-replayed here. Public #5131 still assumes `GeometricCertificates`
  for the general lower bound. None of these results proves the two families.

A useful next input is a checkable arbitrary-centre derivation, or a direct
proof of the two unweighted thresholds using genuine cross-triangle geometry.
For the deletion approach, the specific test is a non-losing fixed-t deletion
on **overweight** configurations, not arbitrary safe ones.
There is no qualified catalog PR, award claim, or change to eligibility.

## Direct unweighted continuation — 2026-11-05

The two unweighted families A and B are the targets; the six-source
payment is one earlier sufficient route. No Lean source changed after
the verified `b24bf60107959020e7b29b6e1263b739509987b0` in this round.
`040c691e903b2d845732914a1a17eb2cb1c0c0fd` records the earlier replay
and evidence, not a second source replay.

- [Affine certificate and narrow-view bound](UNWEIGHTED_AFFINE_THRESHOLD.md):
  for any given set of at least five points with no collinear triple,
  failure of its entire affine class to meet a strict cap above 90° is
  witnessed by at most three actual angles on at most nine points. For
  each target it remains to force such a certificate at its first
  forbidden cardinality. For A an observer's cone of aperture λ/2
  contains at most 2^(n−1) other points; the bound is attained and
  rules out a two-part narrow-view split in a putative counterexample.
- [Wide-sector counterexample](UNWEIGHTED_SECTOR_COUNTEREXAMPLE.md):
  for every n≥64 an ordinary set strictly satisfying A's angle
  hypothesis has a triangle in every open direction interval of width
  π/n. Even a partition into n triangle-free intervals of unequal widths
  need not exist. The construction has fewer than 2^n points.
- [21-row projection cycles](UNWEIGHTED_ROW_CYCLES.md): at least four
  prescribed rows must be discarded, so no 18 of this fixed model are
  simultaneously realizable. Its obstructed quartet has four individually
  realizable triples. This does not exclude an arbitrary 21-point set.

The [exact checker](scripts/check_unweighted_thresholds.py) verifies four
affine optima on historical examples, both saturated narrow views and
all 1,680 angles in a 16-point A(4) check, and five cycles in the pinned
archive. The general arguments above are written proofs, not Lean
theorems. Neither unconditional all-n cardinality bound is proved.
