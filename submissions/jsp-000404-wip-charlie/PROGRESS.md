# JSP-000404 progress

**INCOMPLETE — family A and all original cases through N=40 are kernel-checked.**
2026-11-05, Windows. No complete original-problem theorem or prize submission.

**Historical full-replay source:** `b24bf60107959020e7b29b6e1263b739509987b0`
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
The first exact unweighted family is now proved for every n >= 1. A strict
cap at (1-2/(2n+1))*pi implies cardinality <= 2^n for every finite injective
planar configuration. `PlanarFirstThreshold` closes the actual-point chain
through continuous projection curves, one/two-turn simple cycles, integer
retiming and signed-band packing. `OriginalFirstBranch` proves
`OriginalLowerBound 3` and the exact first branch of the original formula.

The general family B says that a strict cap at (1-1/(n+1))*pi implies
cardinality <= 5*2^(n-2), for n >= 2. Its n=2, n=3, and n=4 cases are now
proved by the five-, seven-, and coherent nine-phase capacities. The general
n>=5 proof remains open; the first unresolved original cardinality is 41.
The older weighted
lower-strip payment route also remains conditional,
but family A no longer depends on that route. The source's arbitrary-centre
induction still supplies neither missing weighted theorem.
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

## Narrow-observer continuation

`e2168310a609cdbc29e987da325856b7e23a87b0` was verified as the clean initial
HEAD, with parent `040c691e903b2d845732914a1a17eb2cb1c0c0fd`; its exact checker
was rerun successfully. That commit and all earlier history are preserved.

[Narrow observer capacity](NARROW_OBSERVER_CAPACITY.md) derives a common
direction interval of width at most pi-3*lambda for points seen narrowly from
both ends of a base edge. Lean checks prove the ordered-direction statement,
the actual coordinate-geometric finite-set bound, and the weighted result for
explicit private-direction families, with standard axioms only. The written
gap construction identifies these families with the old centre exponents,
giving the lower weighted bound when a top-exponent centre exists and the upper
weighted bound when two top-exponent centres exist. That `centreExponent`
connection remains to be formalized. The no-top lower cases and zero/one-top upper cases
remain open. The independent affine audit also confirms fixed-orbit attainment
and explains why positive active-trace balance implies a global optimum.

One-top upper ordered-direction experiments at delta=0.99 returned UNSAT for
the first forbidden residual sizes for n=2,3,4, SAT at residual size 12 for n=4,
and timeout for n=5. These are solver outputs with no Lean proof.

The [separate-affine-map recursion](AFFINE_PARTITION_OBSTRUCTION.md) has now
been refuted at t=23/5 by twenty integer points. All 3,420 parent-angle checks
pass exactly. For each bipartition, 296 rational matrix certificates force an
angle above the child cap in one part's entire affine orbit. The independent
checker exhausts all 524,288 complementary colouring classes. The scalar trace
inequality is formalized separately; the full counterexample's Lean geometry
is pending. The original lower bound remains open. The next live mathematical
target is the one-top upper ordered-direction conjecture and its weighted form.

## Cyclic projection-wire continuation

The paragraphs below record the successive checkpoints before the completed
family-A chain described at the end of this section.

Checkpoint `7091e8ca0f0f1e23d7ad3aead1842dd9ad116fab`, including the preserved
e2168310 history, was pushed and verified against the tracking and remote SHAs.

The [cyclic-wire route](CYCLIC_WIRE_RETIMING.md) gives a proposed general
derivation of threshold A. Its projection graph lies on a reflected strip.
A simple directed cycle would have one or two turns, forcing half-integer
retiming. Integer-band signs then give the dyadic bound. Three new Lean
modules verify the disjoint-path return argument, loop erasure, graph
potentials, and exact half-grid rounding with the graph hypotheses explicit.
The actual projection-graph construction, simple-cycle path extraction, and
incident-sign coding bridge remain to be assembled in Lean. No unconditional
all-n A theorem has yet been kernel-checked. Family B remains mathematically open.

The [direction-order note](DIRECTION_ORDER_RESEARCH.md) also gives an exact
21-row integral-grid obstruction. Each triple is separately realizable after
a small arc expansion, and every unconditional forced-projection graph is
acyclic. A conditional four-cycle excludes joint realization of the twelve
three-arc rows. Its checker and written proof are retained, with full Lean
geometry pending. The standard-library cyclic checker verifies 61 exact
retimings and all 78,268 simple cycles in its selected small examples.

Current verification is scoped in
`verification/cyclic-wires-20261105/README.md`. The earlier full umbrella audit
continues to refer to its recorded immutable source.

The subsequent `IntegralWireCapacity` module kernel-checks integer retiming
and the modular signed-band injection into n-bit words. `DirectionCutOrder`
kernel-checks the moving cut order, adjacent crossing endpoints under strict
betweenness, and reversal between the initial and final cuts. These are
standalone checked modules at this stage. The remaining A bridge consists
of building the cyclic event graph, extracting its one/two-turn simple cycles,
and deriving its local incident-gap inequalities. Family B remains open.
The focused evidence is in `verification/integral-wire-20261105/`.

The next four standalone modules now construct the consecutive-event graph,
prove its connectivity, derive all local gap conditions from integral cyclic
delays, and apply the dyadic code. `OrderedDirectionWires.card_le_two_pow_of_winding`
is the concrete DirectionData reduction. Its remaining premise is that every
nonempty simple cycle of this constructed graph has winding one or two.
`ProjectionStrictWireDirections` proves the local injectivity needed to use
that graph for actual planar AngleCap data. The winding theorem remains open
in Lean, so the all-n A conclusion is still a proof candidate. Focused
verification is recorded in `verification/ordered-wire-20261105/`.

For B, [unit-interval collapse](UNIT_INTERVAL_RETIMING_RESEARCH.md) is a new
unproved induction candidate. A [nine-wire exact obstruction](FORCED_INTERVAL_COMPRESSION_COUNTEREXAMPLE.md)
rules out requiring all crossings in the collapsed interval to be
bichromatic for every fixed schedule. It covers every real phase by exact
affine threshold checks and exhausts all 512 colourings per phase case.
The freely coloured collapse works on that same schedule. The original
upper-strip bound and the free-colour induction remain open.

## Completed first-threshold chain

The continuation after `58f97b1b249c95f1e14ba76b40912350d29af6fa` closes all
geometric premises for actual planar points. `WireCurveTrace` pastes the
actual continuous antiperiodic curves while retaining a half-open arrow
occurrence for every trace point. `WireCurveEmbedding` derives separation
of arrow sources from sorted local events and complete pair-crossing data.
`SimpleWireCycle` uses the nodup vertex list to identify repeated occurrences.
`PeriodicCycleOrder` then forces the winding to be one or two.

`ProjectionWireCurves` proves the exact trigonometric crossing equation.
`OrderedDirectionCurves` applies it to the existing forward polar lift.
`PlanarFirstThreshold` has no geometry, winding, colouring or payment premise
beyond the ordinary point injection and the stated angle cap. Its strict
threshold theorem includes empty and small finite types and all planar
degeneracies. Finite strict-cap slack is proved separately and used explicitly.

`OriginalFirstBranch` matches the audited formula and proves its complete
first branch and N=3. The umbrella now imports this chain. Focused verification
is recorded in `verification/first-threshold-20261105/`. The earlier full-root
audit remains historical evidence at its recorded source.

Continue research on family B. The stronger fixed-schedule interval-colouring
shortcut remains excluded by the nine-wire certificate. A freely coloured
collapse, a prior-retiming version, or a different upper-strip invariant
remains available for investigation.

The latest B continuation studies a sign-preserving encoding by maximal
independent sets of a triangle-free graph on 2n+1 half-grid coordinates.
The Hujter–Tuza extremal count is exactly 5*2^(n-2). After successful finite
tests, a targeted search refuted the fixed-schedule form on nine coherent
wires at period 7/2. An independent exact checker excludes every triangle-free
graph under all 128 coordinate-polarity choices. A canonical retiming of the
same order restores a five-cycle-plus-edge encoding. The remaining candidate
must therefore select a retiming. Its construction remains open. The
formulation, exact obstruction and repair, excluded local-gap and convex-hull
shortcuts, and next obligation are recorded in
`HALF_GRID_INDEPENDENT_SET_RESEARCH.md`.

The selected-retiming investigation now has a written local criterion for
the canonical clock, based on outgoing tight arcs and odd phase increments.
Targeted fixed-schedule failures at N=17, q=9 were repaired in 200 tested
arrays, yielding four distinct canonical row arrays. The canonical constrained
countersearch returned UNSAT at N=9, q=7 and timed out at N=17, q=9. These
solver results and the written criterion remain outside the Lean chain.

Requiring a straight-line separator is also excluded for independent child
retimings. The retained twenty-point witness has 190 such partitions, and
every one has an exact obstructing child cycle at width 18/5. An unrestricted
ten-plus-ten split remains feasible. The independent checker is
`scripts/check_projection_partition_retiming.py`.

Critical-root potentials now provide a second precise clock selection rule.
Tight root paths and a critical cycle certify their attainment and period
optimality. Exact eleven-wire and seventeen-wire examples exclude restricting
the MIS core to five consecutive coordinates, even for this selection rule.
Both admit sparse five-coordinate cores. The independent replay is
`scripts/check_critical_clock_core_obstruction.py`, with evidence under
`verification/critical-clock-core-20261105/`. A written matching simplification
reduces cyclic pair-deletion encodings to the retained odd core and its odd
cyclic gaps. The arbitrary-configuration representation remains open.

## Small odd-phase capacities — 2026-11-05

`SmallOddWireCapacity`, `OddWireSchedule`, and `PlanarSmallOddThresholds`
prove unconditional capacities three and five at strict caps pi/2 and
2*pi/3. `SevenPhaseCapacity` kernel-checks a 42-position binary covering
certificate: each proper partial seven-cycle colouring extends at least
four positions. Disjoint support therefore bounds separated rows by ten.
`PlanarSevenPhaseThreshold` connects that count to every actual configuration
with strict cap 3*pi/4. `OriginalSmallCases` matches the exact original formula
and proves `OriginalLowerBound N` for all 3<=N<=20.

The focused build passed with 3,261 jobs. The imported research closure has
53 modules / 940 declarations / zero unexpected transitive axioms. Every
collected axiom is `propext`, `Classical.choice`, or `Quot.sound`. The updated
umbrella file also compiles. The proof and evidence are
`SMALL_ODD_THRESHOLD_PROOF.md` and `verification/small-odd-thresholds-20261105/`.
Family B for n>=4 and the full original goal remain open.

## Coherent nine-phase capacity — 2026-11-05

The nine-phase branch now proves family B at n=4. Every maximal proper C9
row has a two-position support in an explicit 42-word cover. Separation
gives cardinality at most 21. Saturation forces one of two five-row cores,
via an explicit Boolean case-split proof; triple phase coherence rules out
both cores. This yields capacity twenty. The crucial geometric bridge
retains original pair-direction betweenness through monotone integer
retiming and then reduces it to the phase-order predicate.

`PlanarNinePhaseThreshold` consequently proves the unconditional 4*pi/5
threshold for all finite injective planar configurations.
`OriginalFortyCases` proves every original lower bound for 3<=N<=40.
Family B for n>=5 remains open; the first unresolved original N is 41.

The focused build passes with 3,272 jobs, the transitive imported-closure
audit passes with 64 modules / 1,088 declarations / zero failures, and the
updated umbrella file compiles. The independent finite checker enumerates
all partial rows and all saturated families; all three generated Lean
sources reproduce byte-for-byte. See `NINE_PHASE_CAPACITY_PROOF.md` and
`verification/nine-phase-threshold-20261105/`. This is a research checkpoint,
not a complete original-problem solution or prize submission.
