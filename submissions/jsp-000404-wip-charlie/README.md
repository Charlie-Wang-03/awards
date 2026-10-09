# JSP-000404 research WIP — Charlie downstream

This directory is a research-only Lean workspace for the still-incomplete
JSP-000404 / Erdős 504 / Sendov minimax-angle proof.

## Current gate — Source Closure

Status: **SOURCE_CLOSURE_GATE = OPEN**.

Before promoting this project as a reconstruction/formalization of established
mathematics, the source chain for the arbitrary-cardinality Sendov classification
must be closed.  The Russian 1995 long paper and the 1995 *Acta Mathematica Hungarica*
article have both been audited.  The latter also does not supply the missing
arbitrary-`s` derivation from the induction hypothesis to the asserted
maximizing exponent profiles; its blanket inversion formula additionally
requires a corrected generalized-inverse interpretation.

See `SOURCE_CLOSURE_GATE_2026-09-28.md` for the original gate criteria and
`ACTA_1995_PROOF_DEPENDENCY_AUDIT_2026-09-29.md` for the completed Acta audit.
The source-closure gate remains open pending a gap-free general-`s` proof or an
independent proof repair.  All Lean in this directory remains research-only;
no complete-proof claim is made.

## Scope frozen in this branch

The Lean library currently contains only **closed consequences** that have
already been justified mathematically:

- the small-`delta` arithmetic inequality `2 * delta * lam < lam`;
- the Sendov-normalized inequality `3 * delta * lam < pi`;
- impossibility of three pairwise-distinct sharp centres once every angle at
  each sharp centre is bounded by `delta * lam`;
- in the first branch `delta < 1/2`, two sharp centres leave no room for a
  third top-level centre under the global cap `pi - lam`;
- the weighted Hansel / Erdős--Szekeres partial-code inequality and the exact
  defect form `sum_v (2^(free v) - 1) <= 2^k - |V|`;
- one-missing and all-missing consequences of the weighted defect bound;
- the exact zero-carry identity `ell = (n - Q) + p`;
- unit-deficit rigidity: `ell = 1` forces exactly one positive quotient gap
  and `sum q = n`;
- the fractional remainder budget and exceptional-gap arc budget;
- linearization of a unit-deficit cyclic gap system after cutting at its unique
  exceptional gap;
- the signed projective-interval geometry that turns one short ray interval
  into `ProjectiveCloseAt` and then `SharpAt`;
- `KraftCertificate`, `OrderedEdgeColoring`, and `BinaryEdgePartition`
  interfaces reducing the global sharp bound to explicit partial-code /
  active-colour constructions;
- ordered-direction base capacities `3 -> 3/2`, `4 -> 2`, `5 -> 5/2`,
  and `6 -> 3`;
- binary carry and local gap-merge arithmetic;
- whole-centre exponent monotonicity and +1/+2 merge-gain criteria;
- abstract compensated deletion, including a single-gain payment rule;
- the gain-closed-core minimum-exponent reduction.

No theorem in this branch claims the missing arbitrary-cardinality sharp
capacity bound.

## Deliberately open bridges

The remaining mathematical work is **not** treated as established: admitted WIP theorems explicitly expose their `sorry` obligations; all non-WIP research proofs must remain axiom-audited and `sorry`-free.
In particular, this branch does not yet formalize or assume:

1. the final cyclic-order / ray-representation bridge completing
   `ell_i = 1 -> SharpAt`; all arithmetic and signed-ray geometry around that
   bridge are already isolated in separate modules;
2. the general lower-half capacity theorem;
3. the general upper-half capacity theorem;
4. an existence theorem producing either
   - a compensated deletion, or
   - an adaptive even edge partition with sufficiently many locally missing
     colours,
   from the global ordered-direction / centre-gap geometry.

## Current hard stops and sharpened outlets

The following tempting strengthenings have now been adversarially tested and
must **not** be used as hidden assumptions:

- a fixed standard-band phase need not satisfy every local deficit budget;
- residual edges cannot in general always be absorbed into one of their two
  neighbouring retained colours;
- per-centre phase averaging need not satisfy
  `E_phase 2^(floorExcess b) >= 2^(floorExcess q)`;
- the coarse support inequality `sum_i 2^(-positiveSupport q_i) <= 1` is false;
- an arbitrary deleted centre need not create an exponent gain anywhere;
- the gain digraph need not contain the simple gain-closed core previously
  hoped for;
- the strong deletion-average condition `sum bonus >= W` is false;
- the exact-normalized global critical-turn conjecture
  `sum criticalWidth <= 2*(n+delta)` is false: two concentric regular
  heptagons (outer radius 1, inner radius 0.85, relative rotation pi/7) give
  `t ~= 13.4330`, `delta ~= 0.4330`, but total normalized critical width
  about `31.3191 > 2*t ~= 26.8661`;
- the weaker total critical bad-mass bound `sum badWidth < t` is also false:
  aligned concentric regular 13-gons near radius ratio 0.708 give
  `t ~= 26.4987`, `delta ~= 0.49868`, and summed bad-interval lengths
  about `37.83 > t`; the obstruction intervals overlap heavily;
- even the strengthening `measure(union bad intervals) <= t/2` is false:
  an aligned double regular pentagon near radius ratio 0.4525 gives union
  coverage about `0.6123*t`;
- "full vertex => every radial gap <= 1" is false.  The correct generic
  conclusion is that a full interlacing puts at most one partition boundary
  in each radial gap, while all partition-boundary spacings are <= 1; hence
  each radial gap is strictly shorter than two units and every quotient is
  <= 1.  Thus the Sendov floor-excess exponent is zero.

Closed replacements now available in Lean include:

- exact one-exception boundary domination and exact budget-failure structure;
- a bad local phase loses exactly one floor-excess unit at the exceptional gap;
- at such a bad phase the exceptional quotient is at least two, and the number
  of boundary-hit zero quotient gaps is exactly `(n - sum q) + 1`;
- zero-gain merges are completely characterized:
  no-carry requires at least one zero quotient, while one-carry zero gain
  requires both quotients zero;
- the sharp total-bonus deletion threshold:
  if `W < |V| + sum_r bonus r`, then some deletion is compensated.

The live global routes are therefore:

1. **fixed-phase wrap route:** prove directly that the union of wrap-triangle
   bad-phase intervals does not cover the phase circle.  Total-turn, total
   bad-mass, and half-circle-union bounds are no longer admissible shortcuts;
   any proof must exploit the strong overlap structure of the bad intervals;
2. **full-band / Hansel route:** find a phase with at most one fully specified
   standard-band vertex, or derive an equivalent defect statement.  A full
   generic vertex has zero Sendov floor-excess, but no global phase-existence
   theorem is proved yet;
3. **adaptive even-partition route:** generalize the Erdős--Szekeres narrow
   direction-interval reassignment while preserving bipartiteness/evenness;
4. **compensated-deletion route:** prove a restricted or dichotomic deletion
   theorem from the coupled radial orders of an actual planar configuration.


Numerical falsification is used only to kill over-strong conjectures; passing
random tests is never treated as proof.

### Notation / indexing warning

There are two different integer scales in the full Blumenthal/Sendov story and
they must not be conflated.

Inside Sendov Lemma 4.12,

[
t=u/2=n+delta,qquad n=lfloor tfloor,qquad 0ledelta<1,
]

and the lower-branch generalized-configuration target is

[
|P|=sum_i 2^{k_i}le 2^nqquad(delta<1/2).
]

This `n` is the integer part of the normalized angular parameter `t`.
It is **not** the outer dyadic index `m` used when the final Blumenthal
classification is written in ranges such as `2^m < N <= 2^(m+1)`.

For example, the final critical value just above `2^m` has
`GA = pi * (1 - 1/(2m+1))`, hence `t=2m+1`; therefore the Lemma-4.12
integer is `n=2m+1`, not `m`.

Consequences for this research branch:

- every theorem stated purely as an `n`-bit / `2^n` capacity theorem remains
  mathematically meaningful;
- `CriticalFiberBalance` is an internal critical-capacity counting lemma and
  must not be described as the original Blumenthal `N=2^n+1` case without an
  additional bridge;
- all future prose must distinguish the Lemma-4.12 integer `n=floor(t)` from
  the outer final-classification dyadic index.

### Exact-normalization correction

A later audit identified an important distinction in the numerical
falsification work.

Sendov Lemma 4.12 chooses the parameter u, hence t = u/2 = n+delta, from the
**actual equality**

  GA(V) = (1 - 2/u) * pi.

Several earlier adversarial searches instead fixed a looser external angle cap
and only required the sampled centre set to satisfy that cap.  Such slack-cap
counterexamples are valid against statements claimed uniformly for every
configuration below a fixed cap, but they do **not by themselves** refute a
statement restricted to Sendov's exact normalization.

Accordingly:

- exact algebraic counterexamples and exact-normalized geometric
  counterexamples remain hard stops;
- slack-cap numerical counterexamples are retained only as warnings against
  over-strong cap-uniform lemmas;
- new induction work should preserve an actual maximum-angle witness whenever
  possible.  If at most three top-level rank-one circles contain a maximizing
  angle triple, deleting a different top-level centre preserves the exact
  angle parameter.

This distinction is now part of the frozen research protocol.

## Current research invariant

The published Sendov Lemma 4.12 correctly reduces a perfect generalized
configuration to

`|P| = sum_i 2^(k_i)`

with each `k_i` computed from the cyclic angular gaps at the rank-one centre.
The unresolved step is the claimed global maximization of this weight profile.

The downstream replacement route is deliberately weaker:

1. deleting a centre merges exactly two adjacent gaps at every survivor;
2. the survivor exponent never decreases;
3. two positive adjacent quotients, or a suitable binary carry, force at least
   one exponent unit of gain;
4. if the induced post-deletion weight gain pays the deleted centre, ordinary
   induction on the number of top-level centres closes;
5. alternatively, an adaptive even partition with local active-colour count
   at most `ell_i = n-k_i` closes immediately through weighted Hansel.

This route does **not** require classifying a unique extremal exponent profile.

## Source audit

The relevant primary-source gap is explicit in Sendov's 1995 proof of Lemma
4.12: after concrete calculations for `s = 2,3,4`, the text assumes the
lemma for `s-1` and then states the general maximizing exponent profiles for
`s` without deriving them from the induction hypothesis.  This is the step
that must not be imported as a proved lemma.

Erdős--Szekeres (1960) supplies the independent graph-theoretic engine used
here: even partitions, the `2^n` capacity bound, and the weighted
missing-colour defect.  Their Theorem 2 also demonstrates that narrow direction
intervals may be reassigned between colours while preserving evenness, which
motivates the adaptive-edge-partition branch of the current proof search.

Public partial formalizations were also checked:

- PR #100: exact N=5--10 and dyadic thresholds;
- PR #300: scoped small/dyadic formalization;
- PR #647: eleven-point direction bound and exact N=11--15.

These packages all leave the arbitrary-N classification open.  In particular,
the N=9 and N=11 machine certificates use the same abstract direction model
(range + two-branch triangle constraints) as the current ordered-direction
reduction; they do not reveal an additional geometric hypothesis that would
trivialize the general bridge.

## Reproduction

Pinned toolchain:

- Lean `v4.34.0`
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435`

From this directory:

```sh
lake exe cache get
lake build
```

This environment does not have a local Lean toolchain. GitHub Actions runs
pinned Lean builds on selected modules; check the workflow status at the exact
commit before asserting that an edited module is kernel-checked. Passing a
module build does not establish the still-missing full geometric theorem.


## Explicit end-to-end proof assembly (2026-10-09)

This section supersedes the earlier statement that no theorem-shaped WIP entry
has admitted proof holes. The **mathematical source-closure gate remains OPEN**.

- `JSP000404Research/FullDyadicHallProofInterface.lean`: kernel-checked,
  **conditional**, no proof holes. Separates two outstanding geometric
  predicates: `EveryMinimalHallCoreHasProjectedLoss` and
  `MinimalHallLossSharedMassGeometricExclusion`.
- `JSP000404Research/PlanarLowerBranchFullProofInterface.lean`: kernel-checked,
  **conditional**, no proof holes. Bridges genuine canonical planar centre
  exponents to the `2^n` lower-branch capacity under those two predicates.
- `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`: deliberately
  now contains **one executable `sorry`** for the global completion-defect
  payment inequality; the historical two-hole Hall-G1/G2 decomposition is
  retained only in older audit interfaces. The theorem remains admitted and
  `#print axioms` includes `sorryAx`.
  This is a research-only architectural assembly, not a valid award submission.
- Incremental CI is still strictly hole-free for **all other Lean modules**.
  Its source audit allows a maximum of two `sorry` in the named WIP
  file (currently one), reports them conspicuously, and forbids `admit`.

Even completion of this lower-branch entry will not alone establish the
full JSP-000404 / Blumenthal classification: other parameter branches and
source-closure obligations require separate formal bridges.


### Verified strict non-loss Hall reduction (2026-10-09)

- `StrictNonlossSubsetHallCapacity.lean` proves, WITHOUT sorry, that
  `exponent v < projectedFree C v` at every vertex of any finite subset
  implies weighted Hall expansion for that subset. Its key ingredient is
  the proved retained-completion multiplicity bound of at most two.
- `DirectionDataHallExactNonlossReduction.lean` proves that any actual
  direction-data deficient core has either a projected-loss centre
  (`k=projectedFree+1`) or an exact non-loss centre
  (`k=projectedFree`). A loss-free deficient core must contain the latter.
- `FullDyadicExactNonlossBoundaryInterface.lean` and
  `PlanarLowerBranchExactNonlossBoundaryInterface.lean` are fully checked,
  conditional, hole-free derivations from the **refined G1 exact-boundary**
  predicate plus the still-open G2 shared-mass exclusion.
- The admitted planar lower-branch WIP now imports the refined planar
  interface. Its first explicit `sorry` concerns only exact non-loss
  boundary geometry; its second concerns global loss-centre shared mass.
  `sorryAx` remains present only on the separately identified WIP theorem.

The refined G1 predicate has NOT been established from planar geometry,
and G2 remains open. Thus the lower-branch bound is still conditional,
and the full arbitrary-cardinality JSP-000404 problem is unsolved.

### Residual-active loss-free Hall-core reduction (2026-10-09)

The research module `JSP000404Research/DirectionDataHallResidualActiveBoundary.lean`
now contains three related, explicitly *unconditional-in-their-stated-hypotheses*
Lean proof scripts (no new `sorry`):

1. An inclusion-minimal deficient, loss-free true DirectionData core has an
   exact non-loss vertex with active residual colour.
2. Every vertex of such a core has a **distinct core-internal residual-edge
   neighbour**. The proof combines the true one-layer local capacity,
   minimal-deficiency/private-word loss, and the established rigidity of
   intersecting retained completion cubes.
3. Such a core contains both residual-bit polarities, witnessed by the
   increasing endpoints of a residual edge.

These reductions focus G1 on an internally non-isolated, two-sided
residual-collision core containing at least one exact non-loss vertex.
They do **not** establish the geometric impossibility of that core; the G1
and G2 `sorry` placeholders in `PlanarLowerBranchProofAdmittedWIP.lean`
remain intact.

**Verification update (2026-10-09):** The residual-active,
internal-neighbour, and refined conditional-interface modules WERE
successfully kernel-compiled at commit `8345cb43caf2529de08cc2cf34997713d569699c`
by fast incremental Actions run `37919522605`. Their `#print axioms`
reports contain no `sorryAx`; the WIP conclusion still does. A separate
default-branch scheduled CI fallback exists but is not a replacement for
per-SHA verification.

#### Conditional lower-branch interface now uses the internal-residual G1 target

Two new hole-free *conditional* proof scripts are present:
`FullDyadicInternalResidualExactBoundaryInterface.lean` and
`PlanarLowerBranchInternalResidualExactBoundaryInterface.lean`.
They formally reduce the previous G1 exclusion to the internal-residual
witness version and preserve the separate G2 shared-mass obligation.

`PlanarLowerBranchProofAdmittedWIP.lean` now imports the latter interface.
The number of deliberate executable `sorry` placeholders is STILL TWO:
G1-INTERNAL and G2. These conditional-interface and WIP modules were
targeted-compiled successfully at `8345cb43caf2529de08cc2cf34997713d569699c`
(run `37919522605`). Their *conditional* compilation must not be mistaken
for an unconditional proof. The complete JSP-000404 theorem remains open.


### CRITICAL: genuine DirectionData counterexample to unrestricted Hall G1 (2026-10-09)

**Status: FORMALLY REFUTED for the abstract `DirectionData` interface.
This does NOT refute JSP-000404 or automatically transfer to the planar
`AngleCap` geometry interface.**

Files:
- `JSP000404Research/DirectionDataThreePointG1Audit.lean`: explicit
  `Fin 3` direction data, genuine local cycles, rational gap certificates,
  and both endpoints' retained palettes.
- `JSP000404Research/DirectionDataThreePointG1HallRefutation.lean`:
  exact code/block calculation, a deficient loss-free pair, formal
  `¬ LossFreeMinimalHallInternalResidualExactExcluded`, formal
  `¬ LossFreeMinimalHallExactBoundaryExcluded`, and formal
  `¬ EveryMinimalHallCoreHasProjectedLoss`.
- `JSP000404Research/DirectionDataHallExactCycleTight.lean`:
  prior kernel-checked equality/stepwise-rigidity reduction for hypothetical
  exact-nonloss residual-active minimal Hall cores.

Concrete instance:
- `V = Fin 3`, `t = 23/10`, `n = 2`;
- `D(0,1) = 21/10`, `D(0,2) = 19/10`, `D(1,2) = 1`;
- local cycle exponents `k=(1,0,0)`;
- true loss-free pair `T={0,1}` with demands `2+1=3`,
  `Q_0 = Q_1`, and `card(Q_0 union Q_1)=2`;
- nevertheless `sum_{v in Fin 3} 2^k(v) = 4 = 2^n`.

All DirectionData structure axioms, finite cycle construction, candidate
block calculations, and refutations are theorem-checked. The relevant
incremental Actions runs were `37922162135` (local gap rigidity),
`37924022367` (retained palettes), `37924877907` (internal G1
refutation), and `37925153278` (broad/exact G1 refutations and
true global dyadic equality). All `#print axioms` for these new claims
exclude `sorryAx`.

**Research consequence:** The claim "every inclusion-minimal Hall-deficient
enlarged projected candidate family must contain a projected-loss
centre" is FALSE under the current DirectionData axioms, even when
`t=n+delta` with `0<delta<1/2`. Consequently no proof can discharge
this G1 obligation using *only* those axioms. The candidate-block Hall
expansion approach is stronger than the desired total dyadic inequality,
as demonstrated by the example's exact global equality.

Whether the same obstruction can be realized by genuine planar point
configurations satisfying the *additional* reindexing/cycle constraints
has NOT been Lean-proved or Lean-disproved. G1 at the planar-specific
level still needs a principled re-evaluation, not an attempted proof of
the now-refuted abstract predicate. G2 shared-mass exclusion is also open.
The WIP has now been re-based to one equivalent global-payment `sorry`;
it remains admitted and must not be promoted as a complete proof.


### Current proof architecture — global completion payment (2026-10-09)

**This section supersedes the earlier historical descriptions of G1/G2
as the active WIP proof path.**

The formally verified three-point `DirectionData` counterexample
(`DirectionDataThreePointG1HallRefutation.lean`) has loss-free
subset-Hall deficiency, yet saturates rather than violates the desired
global dyadic bound. Therefore universal minimal-core exclusion at the
bare DirectionData layer is **false**. No planar realizability claim is
inferred from this abstract model.

`PlanarLowerBranchGlobalPaymentReplacement.lean` defines the sound,
non-Hall replacement. It proves both the implication and the precise
equivalence between the planar lower-branch dyadic capacity and

`|overlapCompletionWords| + totalDyadicProfileLoss <=
 (2^n - |coveredCompletionWords|) + totalDyadicProfileSurplus`.

Both theorems have no `sorryAx`; incremental CI
https://github.com/Charlie-Wang-03/awards/actions/runs/37931738861
passed. Importantly, the equivalence proves that this is a **correct
reformulation**, not an independent proof of the outstanding inequality.

The canonical research entry `PlanarLowerBranchProofAdmittedWIP.lean`
has been updated to use this payment interface and now contains ONE
explicit executable `sorry`, audited by incremental CI
https://github.com/Charlie-Wang-03/awards/actions/runs/37932036537.
This change does not reduce the unsolved mathematical difficulty, and
`#print axioms` still includes `sorryAx`. Prior two-hole conditional
interfaces remain available as historical research artefacts, but are
not a valid route using only `DirectionData` axioms.

The next genuine mathematical task is to derive nontrivial planar
constraints that establish the global overlap/loss versus holes/surplus
payment, rather than assuming false subset-wise Hall expansion.
The lower and upper branch global conjectures and the source-closure
gate remain OPEN.


### Exact residual hard-credit and genuine planar carrier (2026-10-09)

**Latest validated mainline at `e8232346ab467f1bb5accbc1534e8aba69989600`.**

The previous "overweight implies a full-band-tight centre" result already
existed in `OverweightTightLocalBand.lean`. Its newer planar lifting was
kernel-verified, but should not be counted as an original new local-tightness
theorem. The following advances sharpen the residual *global* obstruction:

1. `ResidualHardRemainderExactCredit.lean` proves an exact accounting
   identity for `R = totalDyadicProfileSurplus -
   card(strictStrictOverlapWords)`, with `R >= 0`:
   `targetWeight + R + BooleanHoles = 2^n +
   card(saturatedOverlapWords) + totalDyadicProfileLoss`.
   In particular the dyadic target is **equivalent** to
   `card(saturatedOverlapWords) + totalDyadicProfileLoss <=
   BooleanHoles + R`. This keeps the *unspent* surplus discarded by
   the older sufficient hard-remainder criterion
   `card(saturatedOverlapWords) + loss <= BooleanHoles`.
   New theorems passed incremental CI
   https://github.com/Charlie-Wang-03/awards/actions/runs/37937184609
   (3142 jobs; no `sorryAx`).
2. `DirectionDataOverweightRealResidualCollision.lean` strengthens
   "there exists a residual-active saturated centre" to the **real
   carrier** disjunction: overweight implies a projected-loss vertex
   OR a residual edge `u<v` with a Boolean word simultaneously in
   both retained completion cubes and at least one exactly saturated
   endpoint `k(u)=projectedFree(u)` or
   `k(v)=projectedFree(v)`. This uses global hard-word positivity,
   and does not assume the refuted subset-wise Hall G1. Incremental
   CI https://github.com/Charlie-Wang-03/awards/actions/runs/37937588391
   passed (3354 jobs; no `sorryAx`).
3. `PlanarOverweightRealResidualCollision.lean` lifts the above
   necessary condition to **actual injective planar `AngleCap`
   configurations**, using `projectionCutLocalCycle` and the
   proved canonical centre exponent identification. The first
   attempt exposed a Lean rewrite mismatch in a dependent endpoint
   witness, repaired in `e8232346`; CI
   https://github.com/Charlie-Wang-03/awards/actions/runs/37938095651
   passed (3355 jobs; no `sorryAx`).

**Open gap:** Neither the existence of a loss witness nor an actual
saturated residual collision contradicts genuine planar geometry.
The weighted global inequality still needs a geometric injection or
a cancellation/payment mechanism. This is not an independent proof of
JSP-000404; the active WIP still has ONE `sorry`, and its
`#print axioms` still contains `sorryAx`. No complete award
submission should be made on this basis.


### Geometry-facing overweight endgame — verified carrier and phase slip (2026-10-09)

The previous full-band-tight-centre result had already been proved in
`OverweightTightLocalBand.lean`; it is not newly established here.
The new verified geometric reduction keeps **actual cross-centre carriers**:

1. `PlanarOverweightHardCarrierPhaseWitness.lean`, theorem
   `planar_overweight_loss_or_hard_carrier_stepwise_top_witness`:
   if a genuine planar `AngleCap` lower-branch configuration is
   overweight, then either a projected-loss centre exists, OR a
   genuine residual edge `u<v` has a common Boolean completion word,
   its direction-floor is exactly `n`, and one endpoint is exactly
   projected-saturated and has a sorted `InteriorBandGapTight` local
   direction list, last floor `n`, and exact cyclic wrap equality.
   This builds the shared-word witness from global counting and the
   stepwise local geometry from `DirectionDataHallExactCycleTight`.
   GitHub Actions run
   https://github.com/Charlie-Wang-03/awards/actions/runs/37941357663
   completed **successfully (3358 jobs)**; axiom audit has no
   `sorryAx`.
2. `PlanarOverweightGeometricHardDichotomy.lean`, theorem
   `planar_overweight_has_concrete_phase_slip_or_rigid_hard_edge`:
   strengthens the first alternative by producing a centre and two
   **consecutive rays** whose normalized direction gap is in
   `[0,1)` yet crosses exactly one integer band. The second
   alternative is the actual residual carrier and one rigid endpoint
   above. Run
   https://github.com/Charlie-Wang-03/awards/actions/runs/37941965289
   completed **successfully (3359 jobs)**; no `sorryAx`.

The first attempt to import the legacy
`ProjectionSaturatedEndpointDichotomy` exposed previously unverified
Lean errors in its transitive dependencies. The
`ProjectionSaturatedBandEquality.lean` layer has since been
**repaired and kernel-checked** (including four clean `#print axioms`
audits). However, the stronger legacy
`ProjectionSaturatedStepRigidity` /
`ProjectionSaturatedOverlapRigidity` /
`ProjectionSaturatedEndpointDichotomy` chain is **NOT** yet accepted
by the new incremental build; its failures must not be hidden or
described as verified. The canonical endgame reductions above do
**not** import that failing chain.

**Remaining mathematical gap:** an injection or non-double-counting
weighted charge must globally compensate the actual short phase-slip
and rigid residual-carrier obligations with Boolean holes plus all
unused profile surplus. Local rigidity and triangular parity do not
on their own prove this inequality. There remains exactly ONE
executable `sorry` in the admitted
`PlanarLowerBranchProofAdmittedWIP.lean`; the original full
JSP-000404 proof and source closure remain OPEN.


### Residual edges share a sub-half-lambda angular cone (2026-10-09)

New code: `JSP000404Research/PlanarResidualNarrowAngleBand.lean`.
Two theorems have passed Lean kernel and explicit `#print axioms` auditing:

- `planar_standardResidual_edge_narrow_terminal_angle`: for any
  genuine generic-projection residual edge `u<v`, writing
  `phi_e = centreForwardLiftedAngle(u, v)` and
  `beta = projectionAngleBase(genericProjectionSlope(p))`,
  lower-branch normalization `t=n+delta`,
  `0<=delta<1/2`, and `lambda=pi/t` gives

  `0 < pi - (phi_e-beta) <= delta*lambda < lambda/2`.

  This follows from actual planar direction-value representation and
  the standard residual top-band test `n <= D(u,v) < t`.
- `planar_standardResidual_edges_common_narrow_cone`: for ANY TWO
  residual edges `u<v`, `x<y`, their globally oriented lifted
  physical directions satisfy

  `|phi_uv - phi_xy| <= delta*lambda < lambda/2`.

  Endpoints may differ; all residual carriers lie within ONE
  common narrow cone adjacent to the projection seam.

Both results compile with no `sorryAx`; GitHub Actions incremental
Lean CI https://github.com/Charlie-Wang-03/awards/actions/runs/37943504650
successfully completed 3360 jobs on commit `28f2ae0f`.
The single-edge intermediate also passed run
https://github.com/Charlie-Wang-03/awards/actions/runs/37943133299.

**Limit:** near-parallelism does NOT bound the number of overlapping
Boolean completion words or build an injective hole/credit assignment.
The hard payment `saturatedOverlap + profileLoss <= holes + unspentSurplus`
remains the geometrically unproved, equivalent global task.
The admitted lower-branch WIP still contains one executable `sorry`.


### Half-band residual-triangle and crossing-carrier planar gap (2026-10-09)

Three further source-facing modules were built and axiom-audited with
**no `sorryAx`**, without invoking the refuted subset-Hall G1 route:

- `StandardResidualInterval.lean` (previously uncompiled dependency)
  has been repaired using explicit residual-source existential
  witnesses and Boolean contradiction elimination. Its fundamental
  exactly-one-child and source/sink interval theorems passed Lean CI
  https://github.com/Charlie-Wang-03/awards/actions/runs/37945930568.
- `StandardResidualHalfBandTriangle.lean` proves that for ordered
  `u<x<v` with outer residual edge `uv`, when
  `t=n+delta`, `delta<1/2`, exactly one child edge is residual;
  the opposite child direction is **strictly below `n-1/2`** and
  differs from the high child by at least one normalized full unit.
  It preserves more than the old mere non-residual classification.
  Run #37945930568, 3103 build jobs, clean axioms.
- `StandardResidualCrossingHalfBand.lean` proves that for **ordered
  interlaced endpoints** `u<a<v<b` with residual edges `uv`,
  `ab`, the middle edge `av` is residual, both flank edges
  `ua`, `vb` are non-residual, each has normalized direction
  **`< n-1/2`**, and each is one full normalized unit below
  the middle residual direction. Run
  https://github.com/Charlie-Wang-03/awards/actions/runs/37946222191,
  3104 build jobs, clean axioms. "Crossing" here is in the
  projection order, **not** an assertion that planar segments intersect.
- `PlanarCrossingResidualAngleSeparation.lean` applies the crossing
  theorem to the genuine canonical planar generic projection and
  converts the normalized gap to a *physical angular inequality*:
  writing `phi_UA`, `phi_AV`, `phi_VB` for forward lifted
  physical angles and `beta` for the common projection angle base,

  `phi_UA + lambda <= phi_AV`, and
  `phi_VB + lambda <= phi_AV`.

  Moreover the angular distance of each flank direction to the
  common terminal seam is **strictly greater than lambda**:
  `lambda < pi-(phi_UA-beta)`,
  `lambda < pi-(phi_VB-beta)`.
  Run https://github.com/Charlie-Wang-03/awards/actions/runs/37946641373,
  3235 build jobs, successful Lean and clean axioms.

These give **quantitative four-centre geometric restrictions**
for interlaced residual-edge carriers. They should be used in
investigating crossing hard words and potential no-double-charge
paying schemes, but they do NOT bound the number of overlapping
completion words or prove an injection into global holes/unspent
surplus. The lower-branch `PlanarLowerBranchProofAdmittedWIP.lean`
still contains ONE executable `sorry` for the globally open
completion-defect payment. Original JSP-000404 remains unproved
and unrefuted.


### Crossing unsafe hard-word compensation: safe flip OR one exponent unit (2026-10-09)

This is the current, kernel-checked progression beyond merely proving
two flank-angle separations. The following are now compiled and have
explicit `#print axioms` output free of `sorryAx`:

- Repaired `StandardResidualNestedRepair.lean`: replaced an unavailable
  `Finset.inter_eq_empty` rewrite with a direct disjointness proof and
  corrected transport of a shared completion word in the multiplicity-2
  contradiction. Repaired `StandardResidualCrossingRepair.lean` analogously
  in its shared-word contradiction. Both compiled in the successful
  dependency build
  https://github.com/Charlie-Wang-03/awards/actions/runs/37948511374.
- `StandardResidualCrossingHardCredit.lean`: for projection-ordered
  `u<a<v<b` carrying two actual unsafe residual overlap words,
  the forced central edge `av` is residual and both outer flanks
  lie `< n-1/2`, one unit below the central direction. There is the
  **concrete safe-or-credit alternative**:

  `exists c, c notin residualForbidden(B,a,v)` OR
  `exponent(a)+exponent(v)+1 <= n`.

  Corollary: if `n <= exponent(a)+exponent(v)`, the safe local flip
  necessarily exists. Both declarations passed CI
  https://github.com/Charlie-Wang-03/awards/actions/runs/37948511374
  (3147 jobs; no `sorryAx`).
- `PlanarCrossingHardCredit.lean`: passes this statement through the
  genuine injective planar `AngleCap` projection and actual canonical
  `CentreProjectiveCycle` exponents, deriving the one-layer profile
  *from the real local cycles*, not assuming an arbitrary profile.
  For actual unsafe hard overlap edges `uv`, `ab`, it combines

  `phi(ua)+lambda <= phi(av)` and
  `phi(vb)+lambda <= phi(av)`

  with `safe-flip(a,v) OR k(a)+k(v)+1 <= n`.
  Run https://github.com/Charlie-Wang-03/awards/actions/runs/37949305249
  successfully compiled 3343 jobs, clean `#print axioms` on the
  canonical planar theorem.

**Precisely what remains open:** A locally safe flip coordinate is
not necessarily a *global* Boolean hole because other completion cubes
may block it. Likewise, an exponent saving at one middle pair must be
charged injectively and without duplication across potentially many
overlap words/edges. Noncrossing/nested hard-carrier configurations
require their own globally compatible handling. The exact whole-
configuration weighted payment

`card(saturatedOverlapWords)+totalProfileLoss
 <= BooleanHoles+unspentSurplus`

is **not proved**. It is equivalent to the original lower-branch
dyadic target; the canonical WIP continues to contain ONE executable
`sorry`. This progress is a local structure lemma, not a complete
proof or counterexample to JSP-000404.


### Crossing hard-carrier high-mass blocker trichotomy (2026-10-09)

**Verified Lean implementation:** `JSP000404Research/StandardResidualCrossingSafeFlipDescent.lean`,
theorem `DirectionData.crossing_unsafe_hard_high_mass_middle_flip_hole_resolve_or_descend`.
Its final incremental CI
https://github.com/Charlie-Wang-03/awards/actions/runs/37954041759
successfully built **3158 jobs** at commit `7e168bd7ade81d125f08bbfa5863c9dc9d57530e`.
The theorem's explicit `#print axioms` contains only `propext`,
`Classical.choice`, `Quot.sound` — **NO `sorryAx`**.

In actual `DirectionData`, assume `u<a<v<b` and two outer
**unsafe overlapping completion-word carriers** `uv` and `ab`.
Assume the true local one-layer exponent budget, high middle
exponent sum `n<=exponent(a)+exponent(v)`, and, crucially, assume
the middle residual edge `av` is also a **SameRetained** hard pair
with **no common inactive retained coordinate**. Then there exists
an outgoing-at-a, inactive-at-v, locally safe retained colour `c`
such that ONE of the following holds:

1. `flippedRetainedCode(C,a,c)` is absent from the **vertex canonical
   retained-code image**;
2. an interior `a<w<v` produces a residual `wv` edge whose
   endpoints are already `RetainedSeparated`;
3. an exterior `v<w` realizes the flipped canonical code and
   the new retained edge `vw` has strict natural band descent
   `(C.color v w).val < c.val`.

The proof connects the compiled crossing high-mass safe-middle outlet
to existing blocker geometry and a *quantitative* retained-band
descent for an external blocker. This establishes a verifiable
one-step local augmenting-path trichotomy; it **does not** establish
that repeated transitions globally terminate or that any produced
word is a globally unused Boolean completion word.

The transitive dependency chain had previously escaped independent
incremental coverage. This turn repaired and recompiled six modules:

- `StandardResidualOuterSplit.lean`: actual equality of residual
  colour values plus correct classical double-negation for retained
  edges;
- `ResidualHardPairSafe.lean`: correct inactive-to-canonical-bit
  transfer;
- `StandardResidualHardPairSplit.lean`: correct logical conjunction
  association for interior residual filters;
- `ResidualSameCodeUnsafeZero.lean`: explicit finite-set emptiness
  argument and reversed cardinal equivalence;
- `StandardResidualSafeHardDescent.lean`: direct genuine residual
  band bound, explicit `Fin`/real comparison, true retained-colour
  equality, and strict descent;
- `ResidualSafeFlipBlocker.lean`: correctly oriented equalities of
  vertex retained bits and the correct active endpoint.

All these imported modules and the newly created target compiled in
the final successful incremental run above.

**Still open:** The canonical admitted lower-branch WIP retains exactly
ONE executable `sorry` for the globally weighted completion-payment
inequality. Missing are a completion-*cube*-aware anchored-hole/blocker
transition and globally injective, non-duplicating charges across ALL
hard overlap and projected-loss carriers. No full proof or refutation
of JSP-000404 is established.


### Planar crossing hard-carrier safe-flip descent (2026-10-10)

New formally verified file:
`JSP000404Research/PlanarCrossingHardFlipDescent.lean`.

Its theorem
`planar_crossing_unsafe_high_mass_flip_hole_resolve_or_descend`
lifts the pre-existing (previously not independently checked in the
planar canonical exponent setting)
`StandardResidualCrossingSafeFlipDescent.lean` trichotomy to actual
injective planar `AngleCap` data. Under lower-branch
`t=n+delta`, `0<=delta<1/2`, and ordered `u<a<v<b`,
assume unsafe shared-completion hard carriers `uv,ab`, a matching
retained canonical code on the central pair `a,v`, no common inactive
retained coordinate, and high canonical exponent mass
`n<=k(a)+k(v)`. Then there exists an oriented safe coordinate
`c` on `a,v` and exactly the certified *inclusive* alternatives:

* no vertex realizes the one-bit-flipped **canonical retained code**;
* an interior blocker `a<w<v` creates a residual child `w,v`
  with proven `RetainedSeparated`;
* a rightward blocker `v<w` has the flipped code and a retained edge
  whose colour value is **strictly below `c.val`**.

The last alternative supplies a genuine bounded natural-number
rank descent for future augmenting-path arguments. It does NOT
establish termination of a globally compatible reassignment process,
nor an injection into uncovered Boolean completion words: a code
unoccupied by canonical vertex codes can still be contained in an
unrelated retained-completion cube.

CI https://github.com/Charlie-Wang-03/awards/actions/runs/37959953766
successfully built **3353 jobs** on Lean-source commit
`f5b60ec800b13b1debe8204dd18cdd524974f652`. The
`#print axioms` output was `[propext, Classical.choice, Quot.sound]`
with no `sorryAx`. The first attempt was fixed for an explicit
versus implicit `n` parameter mismatch; the mathematical statement
was unchanged.

**Outstanding:** globally control blockers lying in completion cubes
without canonical-code equality, and establish injective
no-double-charge of hard overlap + projected loss against global
holes + unspent surplus. The WIP contains one admitted `sorry`.
