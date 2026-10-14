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


### Finite-colour blocker rank audit, NOT yet a closed augmenting path (2026-10-11)

At the current active source head, `PlanarCrossingHardFlipDescent.lean`
already proves a one-step planar crossing flip trichotomy: the flipped
retained CODE is unoccupied, an interior blocker yields a retained-
separated residual edge, or an external blocker appears to the right
with a lower retained edge colour. Its Lean CI passed on commit
`f5b60ec800b1` (run
https://github.com/Charlie-Wang-03/awards/actions/runs/37959953766).

The new `ResidualRankedFlipTermination.lean` isolates the missing
well-foundedness logic and quantitative cost:

- `rankedFlipReach_terminal`: for an abstract transition relation
  whose every step decreases rank in `Fin n`, every starting state
  reaches a state with **no successor**.
- `rankedFlipReach_eventually_terminal`: if a terminal predicate
  additionally satisfies **actual progress/transition closure** at
  every nonterminal state, a terminal state is reached. This
  progress hypothesis is explicit, not silently assumed.
- `no_unbounded_strict_colour_blocker_descent`: no infinite
  strictly descending sequence of values in `Fin n`.
- `rankedFlipReachSteps_rank_budget`: any sequence with `steps`
  genuine decreasing transitions obeys

  `(rank endpoint).val + steps <= (rank start).val`.

  Hence `rankedFlipReachSteps_lt_color_count` proves
  `steps < n`. This is a **conditional** upper bound on valid
  transitions, not a guarantee that the actual blocker geometry
  supplies another transition.
- `exterior_blocker_descending_edge_not_residual`: whenever
  an external blocker yields `(C.color v w).val < c.val`
  with `c : Fin n`, the edge `v--w` is **not residual**:
  its colour is in the retained range `<n`. Therefore the
  raw external edge is *not* immediately reusable as another
  residual hard-overlap state. A new geometrically valid
  transition/reanchoring lemma is genuinely necessary.

The original three ranking theorems passed
https://github.com/Charlie-Wang-03/awards/actions/runs/38118310246
(3159 jobs, no `sorryAx`). The quantitative step-budget and
non-residual-edge extension passed
https://github.com/Charlie-Wang-03/awards/actions/runs/38118550603
(3159 jobs, no `sorryAx`). The latter non-residual result has
**zero axioms**.

**Remaining gaps (do not conflate):**
(1) transition closure from an external retained-colour blocker to a
new admissible state with a lower `Fin n` rank;
(2) proof that a terminal step produces a globally unoccupied
COMPLETION word or a reusable, injectively charged surplus/defect
payment, rather than merely an unoccupied canonical retained code
or a local retained-separated edge;
(3) consistency across *all* carriers, including nested/noncrossing
patterns and projected loss. Only after these are handled can
`hardOverlap + loss <= holes + unspentSurplus` be discharged.
The admitted planar lower-branch entry still contains ONE `sorry`;
the full JSP-000404 conjecture is not yet proved or refuted.


### Rank-zero flip and cube-only blocker closure (2026-10-11)

The earlier verified planar crossing-hard flip trichotomy ends in:
a canonical **retained-code** vacancy; a retained-separated interior
residual child; or an exterior retained-colour blocker of smaller rank.
It is NOT a theorem that the first outlet produces an uncovered Boolean
**completion-cube** word, nor that the exterior edge can be re-used as a
new residual carrier.

Two new source modules isolate rigorously what follows and what does not.

1. `ResidualRankedFlipTermination.lean` now proves
   `zero_colour_flip_no_external_blocker`,
   `zero_colour_flip_code_hole_or_separation`, and
   `rankedFlipReach_zero_rank_terminal`.
   At rank zero the exterior strict-descent branch is impossible; the
   other two outlets are local and not yet globally payable.
   Verified by fast incremental workflow
   https://github.com/Charlie-Wang-03/awards/actions/runs/38119130475
   on source commit `343631bad0c37c47a47ed62f189fffdf3d4ad75a`
   (3159 jobs; no `sorryAx` in the added declarations).

2. `ResidualCompletionCubeFlipCriterion.lean` proves
   `flippedRetainedCode_mem_cube_iff_base_of_inactive`,
   `flippedRetainedCode_global_hole_iff_active_separator`,
   `code_hole_covered_has_inactive_disagreement`, and
   `canonical_code_hole_global_of_full_retained_active`.
   The key *exact* condition for an actual global hole is an
   active-coordinate mismatch against **each** vertex's completion cube.
   Moreover, if an unoccupied canonical flipped code is nevertheless
   covered, some covering vertex differs in an **inactive** retained
   coordinate. This extracts the precise hidden cube-only blocker which
   any future geometric injection/no-double-charge proof must control.
   The full-active corollary is explicitly conditional and cannot be
   assumed for arbitrary planar configurations.
   Verified by fast incremental workflow
   https://github.com/Charlie-Wang-03/awards/actions/runs/38119367187
   on source commit `26e4c163d5ac88af84dcde55c4a950ade99d88ab`
   (3122 jobs; no `sorryAx` in the added declarations).

**Remaining mathematical gate:** Give an AngleCap/planar-geometric argument
that either excludes the cube-only inactive-coordinate blockers or charges
them injectively, together with nested/noncrossing hard carriers and
projected-loss fibres. This must prove
`overlapCompletionWords.card + totalDyadicProfileLoss <=
(2^n - coveredCompletionWords.card) + totalDyadicProfileSurplus`
without assuming it. The lower-branch admitted WIP still has ONE explicit
`sorry`, the arbitrary-cardinality source-closure gate remains open,
and the complete JSP-000404 conjecture has not been proved or disproved.


### Formal no-go for direct Boolean-hole payment by an oriented safe flip (2026-10-11)

**Critical mathematical correction (kernel-checked).** An oriented safe
retained flip of a same-retained hard pair `a,v` at colour `c` satisfies
`c ∈ outgoingRetained B a` and `c ∉ retainedActive B v`.
Independently of the other geometry, the flipped canonical code
`flippedRetainedCode B a c` MUST lie in the upper endpoint's completion
cube `retainedCompletionWords B v` because every active coordinate
of `v` agrees with the lower endpoint's retained canonical bit and
the single differing coordinate `c` is inactive at `v`.

Consequently this word ALWAYS lies in `coveredCompletionWords B` and
CANNOT pay a global Boolean-hole term. It simultaneously lies OUTSIDE
the lower endpoint's cube because `c` is outgoing (hence active)
at `a`. Thus the local safe flip **migrates between cubes** rather than
creating an uncovered word. This remains true even if *no vertex*
realizes the flipped exact canonical code. No extra AngleCap or Hall
assumption is used to obtain this negative result.

New kernel-checked module:
`JSP000404Research/ResidualSafeFlipCubeObstruction.lean`.

Its six base declarations are:
- `sameRetained_flip_mem_inactive_upper_cube`
- `sameRetained_flip_upper_cube_only_disagreement`
- `sameRetained_flip_always_globally_covered`
- `outgoing_flip_exits_lower_completion_cube`
- `oriented_safe_flip_migrates_cubes_not_global_hole`
- `oriented_safe_flip_code_vacancy_not_global_hole`

They passed fast incremental CI
https://github.com/Charlie-Wang-03/awards/actions/runs/38119910670
(3123 jobs, no `sorryAx`).

The follow-on declaration `zero_rank_safe_flip_cannot_pay_boolean_hole`
combines this obstruction with the previously established rank-zero
trichotomy: the terminal local outlet is a **code vacancy** or a
retained-separated interior edge, and the flipped code is still
**globally covered**. It passed targeted CI
https://github.com/Charlie-Wang-03/awards/actions/runs/38120077115.

**Implication for proof strategy:** A direct injection
`oriented-safe-flip ⇒ uncovered Boolean word` is not merely
unproven; it contradicts the existing formal definitions. Any successful
global payment proof must instead use a genuinely global reassignment,
surplus/defect compensation, or another geometric mechanism controlling
the fixed union of completion cubes. Strict colour rank descent alone
cannot fill this gap. The source comment of
`ResidualSafeFlipBlocker.lean` that previously called a canonical-code
vacancy a "genuine Boolean hole" has been corrected.

The single admitted global-payment `sorry` in
`PlanarLowerBranchProofAdmittedWIP.lean` remains OPEN, and the original
JSP-000404 conjecture remains neither proved nor disproved.


### Planar AngleCap lift of the safe-flip no-hole invariant (2026-10-11)

The no-hole obstruction is now connected directly to the true planar
crossing-hard theorem, without weakening the actual geometry or changing
the original theorem's premises. The new module
`JSP000404Research/PlanarCrossingHardFlipCubeObstruction.lean`
establishes

`planar_crossing_safe_flip_is_covered_or_resolves_or_descends`:

under genuine injective planar `AngleCap`, canonical centre-projective
cycles and exponents, crossing unsafe completion-word carriers
`u<a<v<b`, high middle exponent mass and the explicit central
same-retained/no-common-inactive hard hypotheses, there exists a
locally safe `c` with the previously established trichotomy, AND
`flippedRetainedCode B a c ∈ coveredCompletionWords B`.

The latter membership is UNCONDITIONAL once this safe flip has been
selected. Thus a global hole cannot be obtained by claiming that the
locally flipped canonical code is missing from the image of vertex
canonical codes. At rank zero the exterior branch is impossible, but
the canonical-code-vacancy branch remains **globally covered**.
Therefore a new global compensation/injection argument is required;
the original local rank-descent approach cannot directly establish
the missing global-hole payment.

**Independent CI evidence:**
https://github.com/Charlie-Wang-03/awards/actions/runs/38120257300
successfully built 3357 jobs and verified the theorem with only
`propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).
An isolated style warning about necessary local `letI` instance
declaration is nonfatal. The same workflow's explicit sorry audit
reported exactly one executable `sorry` at
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean:64`,
and **zero** outside that allowed WIP module.

**Research boundary remains unchanged:** The original global payment
inequality, required upper branch, and arbitrary-cardinality
source-closure are still open. This contribution disproves a proposed
DIRECT PAYMENT MECHANISM, not JSP-000404 itself.


### Injective safe-flip double-blocker budget and legacy arithmetic premise audit (2026-10-11)

**Genuine local finite matching (kernel checked).** The module
`JSP000404Research/ResidualSafeFlipDoubleMatching.lean`
takes a fixed same-retained residual pair `a<v` and all oriented safe
colours `c ∈ outgoingRetained C a`, `c ∉ retainedActive C v`.
Every flipped word is covered by the upper endpoint's completion cube.
A flip covered by a SECOND cube yields a STRICTLY INTERIOR residual
blocker `a<w<v` whose edge `C.color a w` equals `c.castSucc`.
Therefore distinct doubly covered colours have distinct blockers.
This provides an actual subtype-valued **injective map**, not a
nonconstructive global Hall hypothesis:

`doubleSafeFlipBlockerMap_injective`

and the sharp local cardinal consequence:

`(doubleSafeFlipColors C a v).card ≤
(interiorResidualBlockers C a v).card`.

The Boolean words obtained by flipping distinct retained colours
are distinct (`flippedRetainedCode_injective_in_colour`).
Every safe flip is singly or doubly covered, so:

`safe_flip_colour_budget_le_singleton_add_interior` proves
`card(safeColours) ≤ card(singletonSafeFlipColors) +
card(interiorResidualBlockers)`.

Consequently
`safe_flip_singly_covered_of_more_colors_than_blockers` shows that
strictly more safe colours than interior residual blockers force a
genuine **singly-covered completion word**. It is still NOT a global
Boolean hole; the upper endpoint covers it. This is a local,
Hall-free matching and counting constraint, not a payment of arbitrary
overlaps/losses.

- First injective matching: successful targeted Lean workflow
  https://github.com/Charlie-Wang-03/awards/actions/runs/38127068295
  (3164 jobs).
- Quantitative singleton and full safe-colour budget:
  https://github.com/Charlie-Wang-03/awards/actions/runs/38127189970
  and https://github.com/Charlie-Wang-03/awards/actions/runs/38127328738
  (3164 jobs each).
- Independent umbrella import target:
  `JSP000404Research.VerifiedOverlapRewire`, successfully built:
  https://github.com/Charlie-Wang-03/awards/actions/runs/38127459009.
  It deliberately does **not** import
  `PlanarLowerBranchProofAdmittedWIP`.

**Legacy Lean fixes and mathematical audit.** We repaired the
definitional/tactic breakages in `KraftBridge.lean` and
`GainCore.lean` (verified by
https://github.com/Charlie-Wang-03/awards/actions/runs/38122127957),
then in `ShortArcTransition.lean`,
`CriticalPhaseInterval.lean`, and `SingleSupportWidth.lean`
(verified by
https://github.com/Charlie-Wang-03/awards/actions/runs/38127626065).
These were not substitutes for geometric proof steps.

More importantly, the TWO old arithmetic equivalences in
`BoundaryExcess.lean` were MATHEMATICALLY FALSE as previously stated,
because they compared truncated natural subtraction without bounding
`floorExcess q` by `n`. In particular, on a one-element index type
with `n=0`, `q(0)=2`, `b(0)=0`, we have
`positiveSupport b=0`, `floorExcess b=0`,
`floorExcess q=1`. Both unrestricted iff statements fail.

`BoundaryExcessMissingPremiseRefutation.lean` formally refutes
the unrestricted theorem statements with no `sorryAx`.
`BoundaryExcess.lean` now includes the ESSENTIAL geometric
premise `∑ i, q i ≤ n` explicitly in
`support_budget_iff_floorExcess_le` and
`support_budget_fails_iff_floorExcess_lt`.
The corrected versions and both refutations passed:
https://github.com/Charlie-Wang-03/awards/actions/runs/38127921869
(3094 jobs, no `sorryAx` in the audited declarations).
This change corrects a false historical AUXILIARY statement.
It does not add assumptions to the main JSP-000404 conjecture.
Any legacy callers must supply this geometric sum bound.

**Important status boundary.** The full legacy
`lake build JSP000404Research` default-target tree has other
unrelated pre-existing source errors and is not a clean proof
acceptance artifact. Only the named module builds above are verified.
The allowed research WIP still contains the single explicit
`sorry` at `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean:64`.
The global completion-payment inequality and the original JSP-000404
problem remain **OPEN**. Local injectivity and a corrected auxiliary
iff do not justify replacing this `sorry`.


### Globally injective hard-to-soft overlap words (2026-10-11, follow-on)

**Global injectivity across ALL source pairs.** The newly verified
`JSP000404Research/ResidualGlobalSafeFlipMatching.lean` derives from
completion multiplicity ≤ 2 that two increasing `SameRetained C a v`
source pairs sharing upper endpoint `v` must share the lower
endpoint `a`. An oriented safe flip of a hard source
`(a,v,c)` whose word remains doubly covered transfers to a
genuinely intersecting residual cube pair `(w,v)`, where
`a < w < v` and `C.color a w = c.castSucc`.
The upper endpoint identifies `a`; the edge colour identifies
`c`. Consequently source triples from *different* hard pairs
cannot double-charge the same residual overlap carrier:

`globalDoubledSafeFlipOverlapEdge_injective`.

More strongly, the target edge `(w,v)` cannot be another
same-retained hard pair, since that would place three distinct
vertices in the same retained canonical-code fibre. The actual
global injective target set is
`softOverlapCarrierPairs`, not all residual carrier pairs:

`globalDoubledSafeFlipSoftOverlapEdge_injective`,
`globalDoubledSafeFlips_card_le_softOverlapCarrierPairs`.

Kernel-verified incremental Lean builds:
- https://github.com/Charlie-Wang-03/awards/actions/runs/38129907921
  (3168 jobs; global residual carrier injection).
- https://github.com/Charlie-Wang-03/awards/actions/runs/38130165074
  (3168 jobs; stronger soft-carrier injection).

**Global Boolean-WORD injection.**
`JSP000404Research/ResidualGlobalSoftOverlapWordCharge.lean`
shows equal flipped words must have equal unique ordered residual
carriers, so carrier injectivity implies *word* injectivity:

`globalDoubledSafeFlipToSoftWord_injective`.

Every output word is still DOUBLY COVERED (by the soft residual
carrier), hence this is a global overlap-to-overlap displacement,
not an uncovered Boolean word:

`(globalDoubledSafeFlips C).card ≤
(softOverlapCompletionWords C).card`.

Verified in
https://github.com/Charlie-Wang-03/awards/actions/runs/38130317381
(3170 jobs).

**Disjoint global hard/soft overlap mass.**
`JSP000404Research/ResidualHardSoftOverlapPartition.lean`
partitions all overlap words by the uniquely determined pair of
completion-cube owners:

`overlapCompletionWords C =
hardOverlapCompletionWords C ∪ softOverlapCompletionWords C`,

and formally proves the parts are disjoint. Therefore

`(overlapCompletionWords C).card =
(hardOverlapCompletionWords C).card +
(softOverlapCompletionWords C).card`.

The global word injection then gives the new certified charge
constraint

`(globalDoubledSafeFlips C).card +
(hardOverlapCompletionWords C).card ≤
(overlapCompletionWords C).card`.

Verified in
https://github.com/Charlie-Wang-03/awards/actions/runs/38130469148
(3171 jobs). The isolated `VerifiedOverlapRewire.lean` library
entrypoint imports ALL three new modules and built successfully
with 3370 jobs:
https://github.com/Charlie-Wang-03/awards/actions/runs/38130629626.
All added printed axioms exclude `sorryAx`.

**Remaining exact obstruction.** This does not prove an
overlap-to-Boolean-HOLE injection, nor payment of a projected-loss
vertex. It controls the *count* of distinct doubled safe-flip source
triples, not the total weighted dyadic mass of arbitrary hard
completion intersections. A new planar/geometric lower bound on
available source safe-flip multiplicity or independent global
surplus/hole credits is necessary before these inequalities can
close the desired `overlap + loss ≤ holes + surplus` step.
The admitted lower-branch WIP, upper branch, and general source
closure remain open. No upstream award PR or unqualified
complete-proof claim follows from this module.


### Whole-face hard-overlap transport and two-layer separation (2026-10-11)

**1. Complete Boolean face, not just canonical safe-flip words.**
`JSP000404Research/ResidualHardOverlapCubeTransport.lean`
defines `flipCompletionWord c` for EVERY Boolean word. For
`c ∈ outgoingRetained C a` and
`c ∉ retainedActive C v`, it is an involution and maps the
ENTIRE intersection `Q_a ∩ Q_v` injectively into the complement
`Q_v \ Q_a`:

`hard_overlap_cube_card_le_upper_only`

and, when the intersection is nonempty,

`2^(commonRetainedInactive C a v).card <= card(Q_v \ Q_a)`.

No canonical-base assumption is used. Verified:
https://github.com/Charlie-Wang-03/awards/actions/runs/38134648974
(3172 jobs; printed axioms exclude `sorryAx`).

**2. Image words cannot participate in ANY hard overlap.**
`JSP000404Research/ResidualHardOverlapCubeSoftRouting.lean`
proves that a same-retained canonical-code fibre has at most
two distinct vertices. If `SameRetained C a v`, no word in
`Q_v \ Q_a` can belong to `hardOverlapCompletionWords C`.
Every complete-face flip therefore lands in the union of
`singletonCompletionWords C` and
`softOverlapCompletionWords C`:

`hard_overlap_full_face_flip_singleton_or_soft`.

For ONE hard pair with an available outward/inactive colour,
the full face mass is bounded by that global target union
size (`hard_overlap_face_mass_le_singleton_add_soft_global`).
Verified:
https://github.com/Charlie-Wang-03/awards/actions/runs/38134963967
(no `sorryAx`).

**3. Residual graph forms two disjoint-cube endpoint layers.**
`JSP000404Research/ResidualIncomingUpperCubeDisjoint.lean`
proves that if `a<v` and `b<z` are residual edges,
then their upper endpoint cubes `Q_v, Q_z` are disjoint
whenever `v≠z`. Symmetrically their lower endpoint cubes
`Q_a,Q_b` are disjoint whenever `a≠b`.
This follows from the forced-residual property of any
completion overlap and the forbidden two-edge residual
path. The two layer-packing theorems are:
`residual_upper_completion_cubes_disjoint` and
`residual_lower_completion_cubes_disjoint`.
Kernel checks:
https://github.com/Charlie-Wang-03/awards/actions/runs/38135128398
and
https://github.com/Charlie-Wang-03/awards/actions/runs/38135498421
(3174 jobs each, no `sorryAx`).

**4. True global mass transport (CONDITIONAL).**
`JSP000404Research/ResidualHardFaceGlobalTransport.lean`
defines the explicit unproved condition
`HasHardOverlapOutgoingTransport C`:

For EACH genuinely overlapping hard residual pair `a<v`,
there EXISTS a retained colour outgoing from `a` which is
inactive at `v`.

Choose one such colour PER HARD PAIR (not per word). Each
hard-overlap word has one unique hard carrier. Use that
carrier's fixed colour flip. Distinct carriers have distinct
upper endpoints by same-code uniqueness; all upper endpoint
cubes are pairwise disjoint by the new two-layer theorem.
Within each carrier, the fixed-colour flip is injective.
This yields a SINGLE GLOBAL injection of EVERY hard-overlap
word into covered singleton-or-soft words, even though each
hard face may have mass `2^d`:

`hardOverlapWordGlobalTransport_injective`,

`hard_overlap_global_mass_le_singleton_add_soft`:

`card(hardOverlapCompletionWords C)
   <= card(singletonCompletionWords C)
      + card(softOverlapCompletionWords C)`.

This is an ACTUAL full-weight global counting theorem under
the stated colour-availability condition, without collisions,
Hall expansion, or a factor of two. The Lean proof itself is
sorry-free; the `HasHardOverlapOutgoingTransport` predicate
is an OPEN additional hypothesis, NOT proved from planar
AngleCap geometry or asserted to be universally true.
Successful CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38135294199
(3175 jobs, audited axioms only propext/choice/Quot.sound).

The independent verified target
`JSP000404Research.VerifiedOverlapRewire` now imports
all of these results and passed:
https://github.com/Charlie-Wang-03/awards/actions/runs/38135645671
(3374 jobs).

**Proof-status boundary:** Full-face transport lands in
SINGLY COVERED or SOFT DOUBLY COVERED Boolean words; both are
still COVERED, not uncovered Boolean holes. No link to
profile-loss payment has been established. It is not valid to
replace the remaining admitted global
`overlap + profileLoss <= holes + profileSurplus` statement
using this conditional theorem alone. In particular, proving
the needed existence of outgoing/inactive retained coordinates
(or deriving a different mechanism for hard pairs lacking them)
and finding actual independent hole/surplus capacity remain
open geometric challenges. The JSP-000404 original theorem,
its upper branch and complete source-closure obligations are
NOT proved. The isolated target is clean; the old comprehensive
legacy module import tree still has unrelated Lean failures.


### Rigid hard-overlap excision and net-payment WIP rewrite (2026-10-11)

**Main achievement: a completely unconditional structural split.**
`ResidualHardOverlapRigidFaces.lean` proves for EVERY
same-retained hard pair `a<v`:

`¬ HasOutgoingHardTransport C a v
 <-> retainedCompletionWords C v ⊆ retainedCompletionWords C a`.

In this no-transport/nested ("rigid") case the ENTIRE upper
completion cube, not merely one canonical Boolean word, is overlapped:

`card(Q_a ∩ Q_v) = 2 ^ projectedFree(C,v)`.

The lower projected-free dimension is >= the upper dimension.
All of these are sorry-free and require no AngleCap input.
CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38143522327
(3176 jobs; no `sorryAx`).

**Exact rigid/transportable dyadic mass accounting.**
`ResidualHardRigidMassAccounting.lean` proves disjointness and
the two exact cardinal identities:

`hardOverlapWords = transportableHardWords ⊔ rigidHardWords`,

`card(rigidHardWords)
 = ∑_{rigid carrier (a,v)} 2 ^ projectedFree(C,v)`.

A rigid face with `projectedFree(C,v) < projectedFree(C,a)`
and `exponent(a) < projectedFree(C,a)` is paid ENTIRELY by
`dyadicProfileSurplus exponent projectedFree a` alone.
If lower-only payment fails and `exponent(a) ≤ projectedFree(C,a)`,
then necessarily either the endpoint free dimensions are equal
OR the lower endpoint is exactly projected-saturated.
This does NOT assume either exceptional case is impossible.
CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38143917102
(3177 jobs; all printed axioms exclude `sorryAx`);
exception isolation:
https://github.com/Charlie-Wang-03/awards/actions/runs/38144517836.

**Critical FALSE route, formally refuted.**
`DirectionDataRigidHardTransportRefutation.lean` reuses the
previously kernel-checked, fully legitimate THREE-POINT
abstract DirectionData profile with cycles exponents (1,0,0),
retained n=2 and the hard edge 0<1. That example has equal
retained active sets and equal canonical codes at 0,1,
a genuinely nonempty hard residual overlap, and NO
outgoing/inactive colour; it is a RIGID nested hard carrier.

`abstract_directionData_refutes_universal_hard_transport`
therefore disproves the previously assumed universal condition
`HasHardOverlapOutgoingTransport` already at the abstract
DirectionData level. This is NOT a counterexample to the actual
JSP-000404 capacity and makes no unproved planar-realizability
claim. CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38144120552
(3406 jobs; no `sorryAx`).

**Unconditional whole-face injection WITHOUT false premise.**
`ResidualTransportableHardGlobalInjection.lean`
chooses one safe coordinate separately for each TRANSPORTABLE
hard carrier, whose definition guarantees that colour exists.
It proves a SINGLE globally injective map from ALL transportable
hard overlap words into singly-covered or soft-overlapped words;
no global colour-availability premise survives:

`card(transportableHardWords)
 ≤ card(singletonCompletionWords)
   + card(softOverlapCompletionWords)`.

Combining the exact partition gives the sharp explicit
rigid remainder:

`card(hardOverlapWords)
 ≤ card(singletonWords) + card(softOverlapWords)
   + ∑_{rigid (a,v)} 2^projectedFree(C,v)`.

These target words are COVERED, not Boolean holes. This
inequality is NOT yet overlap payment.
CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38144316148
(3178 jobs; no `sorryAx`).

**Actual GLOBAL one-sided surplus reservation.**
`ResidualRigidHardSurplusPacking.lean` proves hard carrier
lower endpoints are uniquely assigned: two hard edges can
never share the same LOWER endpoint. Hence the eligible
rigid faces with
`projectedFree(C,v) < projectedFree(C,a)` and
`exponent(a) < projectedFree(C,a)`
can ALL be paid SIMULTANEOUSLY without reusing any lower
endpoint's surplus:

`∑_{eligible rigid (a,v)} 2^projectedFree(C,v)
 ≤ totalDyadicProfileSurplus exponent (projectedFree C)`.

This is more than summing local face bounds without regard
to duplicated budgets: the lower-endpoint map is injective,
as separately Lean-verified.
CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38144696691
(3178 jobs; no `sorryAx`).

**Exact master payment rewrite with an honest NET budget.**
`ResidualRigidPaidDefectReduction.lean` defines
`oneSidedPaidRigidOverlapWords C exponent` as the union of
eligible fully paid rigid overlap cubes, and
`afterRigidPaymentOverlapWords C exponent` as
`overlapCompletionWords C \ oneSidedPaidRigidOverlapWords C exponent`.
The paid words are a proven subset of the actual globally
overlapped words, pairwise disjoint by unique residual carrier.
Their cardinality equals the sum of eligible full upper dyadic
face masses and is no greater than total surplus.

It proves the kernel-checked EQUIVALENCE:

`overlap + loss <= BooleanHoles + surplus`

**if and only if**

`remainingOverlap + loss <= BooleanHoles + (surplus - paidRigidMass)`.

No one-sided rigid-face surplus may be recharged on the remaining
soft/hard/loss obligations. This is a GENUINE, not just verbal,
accounting excision from the unfinished master payment statement,
although the two inequalities remain mathematically equivalent.
CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38144887395
(3179 jobs; five printed kernel axiom audits exclude `sorryAx`).

**Actual PLANAR entrypoint and admitted hole changed.**
`PlanarLowerBranchPaidRigidReduction.lean` is a sorry-free
`AngleCap` bridge:
`planar_lower_branch_dyadic_capacity_of_paid_rigid_remaining`,
whose only additional input is the REDUCED net-payment condition.
It passed:
https://github.com/Charlie-Wang-03/awards/actions/runs/38145050518
(3351 jobs; no `sorryAx`).

The single executable `sorry` in
`PlanarLowerBranchProofAdmittedWIP.lean` has been REWIRED
to exactly this **afterRigidPaymentOverlapWords + loss versus
holes + NET surplus** goal. This was actually Lean-compiled:
https://github.com/Charlie-Wang-03/awards/actions/runs/38145198810
(3352 jobs; the admitted WIP theorem correctly prints `sorryAx`).
No second admitted theorem or hidden hypothesis was added.

The sorry-FREE independent verification umbrella
`JSP000404Research.VerifiedOverlapRewire` imports the
unconditional partition, actual rigid surplus reservation,
new planar bridge, and 3-point nonuniversality refutation,
but NOT the WIP theorem. This whole independent chain
compiled successfully:
https://github.com/Charlie-Wang-03/awards/actions/runs/38145361537
(3418 jobs; no source errors).

**Still unproved:** The remaining net-payment inequality for
genuine planar AngleCap configurations is still equivalent to
the original lower-branch dyadic conjecture. Its overlap
set includes all soft residual overlap words, transportable
hard-overlap words, and rigid words not covered by the
independently one-sided-paid class. Projected profile loss
remains a separate burden. Furthermore, proving separate
surplus payments for the remaining subfamilies does not
suffice unless their budgets are mutually nonduplicative.
The abstract 3-point rigid example cautions against
assuming all rigid cases disappear from DirectionData.
The upper branch and source closure are likewise OPEN.
There is exactly one explicitly admitted lower-branch
mathematical goal; no proof/disproof or prize-eligible
complete submission is claimed. The historical full legacy
Lean import target remains separately broken; only the
named verified entrypoints above are claimed green.


### Expanded hard matching and saturated-hard remainder (2026-10-11)

**A strictly stronger already-paid overlap class.**
The earlier one-sided rigid-face payment has been extended from
one lower-endpoint surplus to TWO-ENDPOINT surplus and then
to ALL hard residual carriers. The crucial mathematical fact is
that hard retained-code carrier pairs are VERTEX DISJOINT:
neither two lower endpoints nor two upper endpoints can repeat,
and a residual upper endpoint cannot be any residual lower
endpoint (this would give a forbidden two-step residual path).

In `ResidualRigidTwoEndpointSurplusPacking.lean`, the theorem
`sum_twoEndpointPayableRigidMass_le_totalSurplus` pays a
complete rigid face when (1) it has a wider strictly-slack
lower endpoint OR (2) its endpoint free dimensions are equal
and BOTH endpoints are strictly slack.
No endpoint surplus is double-counted. Kernel CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38149337075
(3180 jobs, no sorryAx).

`ResidualAllHardSurplusPacking.lean` derives the generic
`hard_carrier_subset_paid_by_pair_surplus` matching principle.
It defines `surplusPayableHardCarrierPairs` containing:
* ANY hard carrier with BOTH endpoints projected-strict, even
  if it is NOT rigid and has no canonical flip mechanism;
* rigid nested carriers with a STRICTLY larger lower free
  dimension and strictly-slack lower endpoint.

Their COMPLETE overlapping Boolean-face mass satisfies
`sum_surplusPayableHardMass_le_totalSurplus` with globally
disjoint endpoint surplus accounts.
Under the standard vertex projected-free profile budgets,
`hard_not_payable_implies_endpoint_saturation` proves that
each carrier outside this class has AT LEAST ONE projected
saturated endpoint. Kernel CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38149542281
(3181 jobs, no sorryAx).

**Actual global surplus reservation and exact unpaid-words
decomposition.** In `ResidualAllHardPaidDefectReduction.lean`,
`surplusPaidHardOverlapWords` is the union of the complete
overlap intersection faces of ALL surplus-payable hard carriers.
Because the carriers uniquely own overlap words,

`card(surplusPaidHardOverlapWords) =
  sum_{p ∈ surplusPayableHardCarrierPairs}
  card(carrierOverlapWords(p))`,

and this cardinality is at most the **total original profile
surplus**. The earlier one-sided rigid reservation is INCLUDED
as a literal subset. The universal original payment is equivalent
to

`card(afterAllHardPaymentOverlapWords) + profileLoss
  <= BooleanHoles
     + (totalSurplus-card(surplusPaidHardOverlapWords))`.

The subtraction on the right RESERVES the exact paid amount
and prevents later proof steps from reusing it. Kernel CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38149727925
(3182 jobs, no sorryAx).

`ResidualSaturatedHardRemainder.lean` further proves a
DISJOINT, exact Boolean-word partition

`afterAllHardPaymentOverlapWords =
  softOverlapCompletionWords ∪ unpaidHardOverlapWords`,

so the ONLY remaining overlap count is

`card(softOverlapCompletionWords)
   + card(unpaidHardOverlapWords)`.

Every unpaid hard Boolean word has a unique hard residual
carrier NOT in the surplus-paid class. Under
`∀v, exponent(v)≤n` and the one-layer active-colour budget
`card(active(v))≤n-exponent(v)+1`, that unique carrier MUST
have at least one projected-saturated endpoint:
`unpaidHardWord_has_saturated_endpoint`.
These are explicit premises of the saturation theorem; the
general Boolean partition itself has NO such premises.
Kernel CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38150019688
(3183 jobs, no sorryAx).

**Real planar bridge and single admitted WIP.**
`PlanarLowerBranchSaturatedHardReduction.lean` is a
SORRY-FREE kernel-checked planar implication from precisely

`card(softOverlapWords) + card(unpaidHardWords) + profileLoss
  <= BooleanHoles
    + (totalSurplus-card(surplusPaidHardOverlapWords))`

to the lower-branch dyadic capacity. It is STILL logically
equivalent to the previously open lower-branch payment and
DOES NOT assert this narrowed payment as a theorem.
CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38150147747
(3355 jobs; imported chain clean).

The sole admitted
`PlanarLowerBranchProofAdmittedWIP.lean` was actually
rewired to use the newer bridge with precisely ONE remaining
executable `sorry`. Its build succeeded:
https://github.com/Charlie-Wang-03/awards/actions/runs/38150332856
(3356 jobs). IMPORTANT: `#print axioms` on this admitted
WIP DOES report `sorryAx`, as expected. A successful
compilation of an admitted theorem is NOT a proof.

The separate `VerifiedOverlapRewire.lean` entrypoint
imports the new unpaid-hard reduction AND its non-admitted
planar bridge, while EXCLUDING the WIP. It builds successfully:
https://github.com/Charlie-Wang-03/awards/actions/runs/38150496576
(3423 jobs, no source errors).

**Precise still-open mathematical frontier:**
Remaining payment concerns (i) SOFT overlap words,
(ii) HARD overlap words whose unique carrier is not
surplus-payable and, under the one-layer budget, has a
projected-saturated endpoint, (iii) projected profile LOSS,
all payable only with TRUE ambient Boolean holes and
surplus NET of all already paid hard faces. No local
singleton-completion word is counted as a Boolean hole.
The 3-point abstract DirectionData countermodel still
shows that requiring EVERY hard carrier to have an
outgoing/inactive flip is FALSE at that abstraction level.

This is a proper division and independent certification
of the easy hard-overlap MASS, but it does NOT close the
global geometry. The original JSP-000404 conjecture,
its upper branch, and general source closure remain OPEN.


### Unpaid-rigid exponent ascent and fully strict profile subcase (2026-10-11)

**New hard-carrier obstruction classification, kernel checked.**
`JSP000404Research/ResidualUnpaidRigidSaturation.lean` proves that any
unreserved *rigid* hard carrier `(a,v)` satisfying the ordinary projected
free-budget bound must either have a **projected-saturated lower endpoint**
`k(a)=nu(a)`, or have **equal projected-free dimensions**, a saturated
upper endpoint, and **strict exponent ascent**:

`nu(a)=nu(v), k(v)=nu(v), k(a)<k(v)`.

This refines the generic "some endpoint is saturated" result, and identifies
a precise ascent pattern which any further geometric exclusion/payment
argument must handle. It does **not** establish that the ascent is impossible.
Its two printed theorem axiom lists have no `sorryAx`.
Verified: https://github.com/Charlie-Wang-03/awards/actions/runs/38152473441
(commit `5e11c8716ade988a7264bd81ca5e208de2d264e6`).

**Strict-profile payment check, kernel checked after Lean repairs.**
`JSP000404Research/ResidualStrictProfileSoftHoleCapacity.lean` proves:
- if `k(v)<projectedFree(v)` at every vertex, every hard carrier is
  globally surplus-payable, so `unpaidHardOverlapWords=∅`;
- all projected-profile loss is zero in this regime;
- under the **explicit additional** assumption
  `card(softOverlapWords) <= card(BooleanHoles)`, the dyadic capacity
  `sum_v 2^k(v) <= 2^n` follows using the already-certified
  overlap reservation and **net** surplus.

The soft-hole hypothesis is NOT proved from planar geometry here.
Moreover the repository's earlier
`StrictNonlossSubsetHallCapacity.strict_nonloss_subset_enlarged_hall_expansion`
already gives a stronger route in the fully strict profile regime.
Consequently the new strict-profile file should be understood as a
cross-check of the *new accounting decomposition*, **not** a breakthrough
on the remaining saturated planar obstruction.

The initial Lean errors in the strict-profile module (missing
`LinearOrder V`, invalid `Finset` simplification, and an unclosed
empty-finset membership contradiction) were diagnosed from CI logs and
repaired without `sorry` or added axioms.
Verified: https://github.com/Charlie-Wang-03/awards/actions/runs/38153088909
(commit `9198cf6915dfc5d206d1defdd476e25ee6ca1b55`,
3 printed axiom lists: `[propext, Classical.choice, Quot.sound]`;
3,185 build tasks, success).

**Open gates remain unchanged.**
`PlanarLowerBranchProofAdmittedWIP.lean` has **one intentional executable
`sorry`** for soft plus saturated-hard plus projected-loss payment against
true holes and surplus NET of paid hard faces. That premise is still
equivalent to the original planar lower-branch dyadic capacity. The
general upper branch, source-closure gate, and historical full root import
remain unverified/broken as documented elsewhere. No complete JSP-000404
proof, refutation, or prize-eligible submission is claimed.


### Net ascending-rigid partial-reservation frontier (2026-10-12)

**New concrete proof chain; the sole planar sorry is still OPEN.**

New `ResidualUnpaidRigidExactDebt.lean` proves for an UNPAID rigid
hard carrier `a<v` with `k(a)<nu(a)` and `k(v)<=nu(v)`:

1. `Q_a = Q_v`, `nu(a)=nu(v)=k(v)`;
2. `card(Q_a inter Q_v) = surplus(a) + surplus(v) + 2^k(a)`;
3. `surplus(v)=0`, so the exact positive local deficit after using
   the lower surplus is **one lower TARGET weight** `2^k(a)`.
   Neither endpoint surplus alone or together pays the whole overlap.

The three theorems were kernel-compiled at
https://github.com/Charlie-Wang-03/awards/actions/runs/38154573428
(3,185 tasks; printed axioms: `propext`, `Classical.choice`,
`Quot.sound`; **no `sorryAx`**).

**Global simultaneous non-reuse is certified**, not assumed.
`ResidualUnpaidRigidPartialReservation.lean` establishes a weighted
hard-carrier matching lemma for arbitrary nonnegative pair charges,
then selects `A = ascendingUnpaidRigidCarriers C k`, disjoint
from earlier whole-face paid carriers `P`. It proves

`paidHardWords.card + sum_{p in A} surplus(k,nu,p.lower)
    <= totalSurplus(k,nu)`.

It further proves

`sum_{p in A} card(carrierOverlapWords p)
  = sum_{p in A} surplus(k,nu,p.lower)
    + sum_{p in A} 2^k(p.lower)`.

All three relevant axiom audits exclude `sorryAx`; CI
https://github.com/Charlie-Wang-03/awards/actions/runs/38154762259
(3,186 tasks, SUCCESS).

**Exact global Boolean word subtraction, not a loose cost bound.**
`ResidualUnpaidRigidNetPaymentReduction.lean` proves the selected
ascending-rigid Boolean overlap faces are a subset of the genuinely
unpaid hard words, each face is globally disjoint from other such
faces, and the selected word cardinality equals its precise
carrier mass. Its theorem
`completion_defect_payment_iff_after_ascending_partial_credit`
establishes an EQUIVALENCE between the previous residual payment and

`softOverlap.card
 + (unpaidHardOverlapWords \ ascendingUnpaidRigidWords).card
 + sum_{p in A} 2^k(p.lower)
 + projectedProfileLoss
 <= BooleanHoles
    + (totalSurplus - alreadyPaidHardMass
                    - sum_{p in A} surplus(k,nu,p.lower))`.

The inequality uses TRUE ambient Boolean holes and only NET surplus
after BOTH globally collision-free reservations. It remains
equivalent to the original lower-branch dyadic goal.
Kernel build https://github.com/Charlie-Wang-03/awards/actions/runs/38154972627
(3,187 tasks, all four printed theorems without `sorryAx`).

**Genuine planar entry and sole admitted WIP updated.**
`PlanarLowerBranchAscendingNetPaymentReduction.lean` is a fully
checked, sorry-free `AngleCap` bridge from the above refined
net-payment inequality to the canonical planar centre-exponent
dyadic capacity; kernel CI
https://github.com/Charlie-Wang-03/awards/actions/runs/38155186676
SUCCESS.
The research-only `PlanarLowerBranchProofAdmittedWIP.lean`
now uses this new bridge with its exact reduced net-payment
condition as its **ONE AND ONLY executable `sorry`**; CI
https://github.com/Charlie-Wang-03/awards/actions/runs/38155326727
SUCCESS. Its `#print axioms` still correctly includes `sorryAx`;
a passing WIP build is NOT an unconditional proof.

**Sharpened terminal hard-carrier dichotomy.**
Under the normal one-layer residual-active profile budget,
`ResidualUnpaidHardTerminalClassification.lean` proves that
EVERY unpaid hard Boolean word NOT in the ascending-rigid faces has
a hard carrier that is either:

- outward/inactive-flip TRANSPORTABLE; or
- RIGID with a projected-SATURATED **LOWER endpoint**.

In particular no strictly-slack-lower rigid carrier remains wholly
unclassified: it is now represented by the exact target-weight debt.
CI https://github.com/Charlie-Wang-03/awards/actions/runs/38155465653
(3,188 tasks, both printed theorems without `sorryAx`).

The sorry-free independent `VerifiedOverlapRewire.lean` umbrella was
updated to import the complete new chain, but deliberately NEVER the
admitted WIP. The historical root `JSP000404Research.lean` and full
legacy import remain separately unverified/broken.

**Still-open genuine mathematical step:** establish from actual planar
`AngleCap` geometry the new net payment inequality covering soft
overlaps, transportable unpaid hard words, rigid lower-saturated
unpaid words, the exact ascending-rigid lower target-weight debt,
and projected-profile losses, using genuine Boolean holes and the
remaining non-double-counted surplus. All equivalence reductions
remain necessary accounting, not a proof of the inequality.
Other parameter branches and Sendov/source-closure remain OPEN.
This research is NOT ready for a prize submission.


### Both mixed-rigid partial credits and doubly-saturated terminal frontier (2026-10-12)

**Status:** New research reductions are kernel checked; the planar lower-branch payment goal remains OPEN, and its single executable `sorry` remains in `PlanarLowerBranchProofAdmittedWIP.lean`. This section supersedes the preceding *ascending-only* frontier as the most refined WIP objective, but does NOT supersede any historical proof files.

**New exact descending-rigid case.** `ResidualDescendingRigidExactDebt.lean` proves that any rigid hard carrier `(a,v)` with `k(a)=nu(a)` and `k(v)<nu(v)` satisfies

`card(Q_a inter Q_v) = dyadicSurplus(v) + 2^k(v)`,

and the full face CANNOT be covered by its two endpoint surpluses. The strict endpoint's exact unpaid target weight is `2^k(v)`. The descending selected family is disjoint from previously full-face paid carriers and from the earlier ascending-rigid family. CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38194200004 (PASS; four printed axioms exclude `sorryAx`).

**Global triple-family collision-free matching.** `ResidualBothMixedRigidSurplusPacking.lean` adds the third non-reusing credit class. With `P` old fully paid hard carriers, `A` unpaid ascending rigid carriers (strict LOWER), and `B` unpaid descending rigid carriers (strict UPPER), it proves

`paidHardMass + sum_A surplus(lower) + sum_B surplus(upper) <= totalSurplus`.

The first CI run found one Lean arithmetic-normalization proof error; this was repaired in `cfdeeea93204d5e0e2eaa1de49bbe9a8f55c5f6c`. The downstream `ResidualBothMixedRigidNetReduction.lean` then passed its own kernel CI together with all imports at https://github.com/Charlie-Wang-03/awards/actions/runs/38194527651 (3,190 jobs).

**Actual Boolean words, exact net debt, not a double-counted sum.**
`ResidualBothMixedRigidNetReduction.lean` establishes global disjointness of `ascendingUnpaidRigidWords` and `descendingUnpaidRigidWords`, individual union-cardinal identities, inclusion in genuinely unpaid hard overlap words, and the *exact equivalence* between the preceding lower-branch payment criterion and the further reduced one:

`softWords.card
 + remainingUnpaidHardAfterMixedRigidWords.card
 + sum_A 2^k(lower) + sum_B 2^k(upper)
 + projectedProfileLoss
 <= trueBooleanHoles
    + totalSurplus - paidHardMass
                   - sum_A surplus(lower)
                   - sum_B surplus(upper)`.

Subtraction is natural-number truncated subtraction, with sufficient budget inequalities already kernel proven. The new equivalence theorem prints exactly the standard `propext`, `Classical.choice`, `Quot.sound` axioms; NO `sorryAx`.

**Sharper structural terminal class.** Under the same ordinary one-layer residual-active profile budget as before, `ResidualTerminalDoubleSaturatedHard.lean` proves that every Boolean word in `remainingUnpaidHardAfterMixedRigidWords` is uniquely owned by a hard carrier which either (i) has an outward/inactive transport, or (ii) is rigid AND **both endpoints** satisfy `k=nu`. In particular any rigid hard carrier remaining after BOTH partial credits is doubly projected-saturated, whereas formerly only lower-endpoint saturation was known. CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38194693776 (PASS, 3,192 jobs, both theorem axiom lists exclude `sorryAx`). This classification does not imply that the transport image is uncovered or that double saturation is impossible for all planar point configurations.

**Planar connection and honest admitted boundary.**
`PlanarLowerBranchBothMixedNetPaymentReduction.lean` is a sorry-free verified bridge from the refined genuine-plane `AngleCap` net-payment input to the planar lower-branch dyadic capacity. CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38194845553 (PASS). `PlanarLowerBranchProofAdmittedWIP.lean` now uses this bridge with exactly ONE executable `sorry`, whose axiom report correctly includes `sorryAx`. CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38194983095 (PASS, 3,366 jobs; admitted theorem remains NOT a proof). `VerifiedOverlapRewire.lean` now imports every new sorry-free module and EXCLUDES the admitted WIP; CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38195143803 (PASS).

**Remaining mathematical obligation.** Construct a genuine global planar-geometric payment of SOFT overlap, all unpaid TRANSPORTABLE hard mass, all DOUBLY SATURATED rigid hard mass, the two mixed-rigid STRICT-ENDPOINT target debts, and projected profile loss, against TRUE Boolean holes plus the verified net remaining surplus. This is still EQUIVALENT to the previously open lower-branch sharp capacity. The general upper branch, the legacy full-root build and the source-closure/prize-submission gates are NOT claimed closed.


### Genuine-planar two-tight terminal hard carrier frontier (2026-10-12)

**Certification scope:** The recent accounting frontier remains the exact BOTH
mixed-rigid net payment in `PlanarLowerBranchProofAdmittedWIP.lean`.
There is still exactly **one admitted executable `sorry`** at this
equivalent planar global defect-payment inequality. Its `#print axioms`
continues to include `sorryAx`. Neither this section nor the new files
constitutes a complete solution or disproof of JSP-000404.

**New genuine geometry, not a repeated accounting tautology:**
`PlanarRemainingRigidTwoCycleTight.lean` proves that an actual remaining
rigid hard Boolean word, in a genuine planar `AngleCap` configuration
with `t=n+delta`, `0<=delta<1/2`, forces **BOTH endpoints** of its
unique rigid carrier to have independently stepwise-tight local
projective direction cycles. At each endpoint `i`, the actual
`projectionCutLocalCycle` has values `a_i::xs_i` satisfying
`InteriorBandGapTight a_i xs_i`,
`floor(xs_i.getLastD a_i)=n`, and
`excess(floor(a_i+t-xs_i.getLastD a_i))=floor(a_i)`.
This uses real `centreExponent`, the planar one-layer budget, the
residual top-band incidence and the verified exact local-cycle theorem.
CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38196290358
(3,407 jobs, successful; one printed theorem with the standard
`propext/Classical.choice/Quot.sound` axioms and NO `sorryAx`).

`PlanarRemainingHardTwoCycleDichotomy.lean` elevates the above to
EVERY genuinely unpaid hard-overlap Boolean word after both mixed-rigid
partial payments: either its carrier has a safe outward/inactive
transport, or a rigid carrier owns the word and BOTH its genuine
local cycles have the three stepwise/top-band/wrap certificates.
The second case is a necessary two-centre geometric obstruction.
It has NOT been shown impossible for all planar configurations.
CI (also covers the next file):
https://github.com/Charlie-Wang-03/awards/actions/runs/38196515601
(3,409 jobs, successful; axiom audit excludes `sorryAx`).

**Exact terminal rigid mass.**
`ResidualTerminalRigidExactUnpaidMass.lean` proves that for a terminal
rigid Boolean word under the usual one-layer budget,

`card(carrierOverlapWords(p)) = 2^k(p.upper)`,

`k(p.upper)<=k(p.lower)`, and BOTH endpoint dyadic surplus values
equal zero. The face's entire upper target weight is genuinely
unpaid locally; reusing endpoint surplus would be incorrect.

**Carrier-level classification WITHOUT selecting any Boolean word.**
`ResidualCarrierLevelFourWayClassification.lean` strengthens the
prior Boolean-word classification, using ONLY hard-carrier membership
and the two endpoint projected budget conditions. Every genuinely
unpayable hard carrier belongs to one of FOUR classes:

1. safe outward/inactive transportable;
2. ascending mixed rigid, strict LOWER endpoint, certified partial credit;
3. descending mixed rigid, strict UPPER endpoint, certified partial credit;
4. doubly projected-saturated rigid.

For a rigid carrier outside both mixed-rigid and whole-face paid
families, no overlap word is needed to prove that both endpoints
are saturated, its full face has mass `2^k(upper)`, and its two
surpluses are zero. The first CI run found a Lean expression
mismatch between `carrierOverlapWords` and the defining finite-set
intersection when rewriting cardinality. Repaired by explicitly
normalizing the carrier face expression at commit
`7af6f44a17808e9b5bbf0248f8518c2b2a44a4fe`.
CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38196825275
(3,194 tasks, successful, four axiom audits without `sorryAx`).

**Independent Lean integration:** `VerifiedOverlapRewire.lean`
now imports all new modules and continues to EXCLUDE the admitted WIP.
The umbrella successfully compiled **3,450 jobs**:
https://github.com/Charlie-Wang-03/awards/actions/runs/38196962349.

**Remaining mathematical bottleneck:** From the TWO tight-cycle
conditions at real planar terminal rigid carriers, prove a new
cross-centre geometric impossibility, a non-reusing transition
strictly decreasing a well-founded obstruction, or a globally
injective payment into TRUE Boolean holes or verified unreserved
surplus. The already proved transport of movable hard faces into
singleton/soft-overlap COVERED words is NOT a hole injection.
Soft-overlap mass, projected-profile loss, both mixed-rigid target
debts and double-saturated rigid mass remain in the sole global
payment `sorry`. Other parameter branches, historical monolithic
root compilation and source-closure remain open.


### Exact terminal hard-face ownership and sharp five-source payment frontier (2026-10-12)

**Current proof status:** STILL OPEN. The true-planar lower-branch entry
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` contains
**exactly ONE executable `sorry`**, and its `#print axioms` correctly
reports `sorryAx`. The new work below is verified **without** admitting
this global geometric inequality. No complete proof, disproof, award
submission or source-closure is claimed.

**New hard Boolean-word decomposition.**
`ResidualTerminalHardCarrierPartition.lean` (commits
`939e42adf991d657cb178b5a234c65df267c494c` and corrective
`abcf003c080d84cd30970756f686dc732bcf53c1`) proves that
the unreserved hard Boolean words after FULL paid carrier reservation
and BOTH mixed-rigid partial credits comprise an EXACT, DISJOINT
whole-face partition:

`remainingUnpaidHardAfterMixedRigidWords =
 netTransportableHardWords ∪ netRigidHardWords`

with disjointness, not just a cardinal upper bound. In particular,
the subtraction of old paid and both mixed-rigid face sets does
not accidentally subtract parts of an unrelated carrier's face.
The proof uses unique ORDERED hard carrier ownership for EACH
Boolean word. The transportable subset injects into already
COVERED singleton/soft words and is bounded by their cardinality,
but these sinks are NOT necessarily true Boolean holes.
Successful CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38198609641
(3,196 jobs; six theorem axiom audits exclude `sorryAx`).

**Exact terminal rigid target mass.**
`ResidualTerminalHardNetPaymentReduction.lean` proves that the
standard one-layer residual-active budget at a hard carrier's
endpoints follows from residual top-colour membership. Thus

`card(remainingUnpaidHardAfterMixedRigidWords) =
 card(netTransportableHardWords)
 + SUM_(p in netRigidHardCarriers) 2^k(p.upper)`.

All terminal rigid faces are doubly projected-saturated and have
zero endpoint surplus. This identity yields an exact equivalence
between the preceding both-mixed-rigid net inequality and the
five-source inequality below; it does NOT itself establish the
inequality. Successful CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38198809573
(3,197 jobs, four theorem axiom audits without `sorryAx`).

**Sharper terminal rigid geometry/combinatorics.**
`ResidualTerminalRigidTwinCubeDichotomy.lean` proves a certified
carrier-level dichotomy:
- EQUAL endpoint target exponents: the two retained completion
  Boolean cubes are LITERALLY identical, as are the two
  retained-active coordinate supports;
- UNEQUAL target exponents: strict DOWNWARD exponent descent from
  lower carrier endpoint to upper carrier endpoint.

This derives from rigid upper-cube inclusion, projected-free
equality and the one-layer double-saturation condition. It is a
necessary structural reduction; it does not eliminate the
twin-cube case or prove an injective global hole payment.
Earlier failed CI attempts revealed projectedFree rewrites and
missing reflexive inequality in a `calc` chain; fixed in
`3df598189eafc6d6026ba700c5dd94e1ca2a9bfb`.
Successful CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38199549518
(3,198 jobs, three theorem axiom audits without `sorryAx`).

**Genuine planar bridge + sole admitted WIP.**
`PlanarLowerBranchTerminalHardNetReduction.lean` derives the
standard one-layer profile budget from actual planar `AngleCap`
geometry, uses the exact terminal hard dyadic decomposition,
and proves the new five-source inequality IMPLIES lower-branch
dyadic capacity. Successful CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38198976935
(3,375 jobs; no `sorryAx`).
The WIP entry was changed to call this more explicit bridge at
`d398eaf90fd8e0d0c25de50e911c1c289e5da2d0`, and its
verification CI succeeded:
https://github.com/Charlie-Wang-03/awards/actions/runs/38199139751
(3,376 jobs; WARNING of precisely ONE `sorry`, `sorryAx` remains).

In symbolic form, the sole OPEN global geometric inequality is:

`softMass
 + netTransportableHardMass
 + SUM_terminalRigid 2^k(upper)
 + SUM_ascendingMixed 2^k(lower)
 + SUM_descendingMixed 2^k(upper)
 + projectedProfileLoss
 <= TRUE Boolean holes
    + totalProfileSurplus - reservedFullPaidHardMass
                          - reservedAscendingLowerSurplus
                          - reservedDescendingUpperSurplus.`

This five-source inequality is **mathematically equivalent** to the
previously unproved lower-branch bound, not a resolved proof.
The new exact split removes ambiguous hard remainder terminology
but does not manufacture holes or reuse paid surplus.

**Integrated no-sorry verification:** `VerifiedOverlapRewire.lean`
includes ALL new modules listed above, excludes the admitted WIP
and passed independent Lean build at
https://github.com/Charlie-Wang-03/awards/actions/runs/38199725961
(**3,455 Lean build tasks**, no new `sorryAx` in imported lemmas).

**Unresolved conceptual target:** Prove a GENUINE planar cross-centre
incompatibility, a well-founded source-to-sink cascade, or a global
injective payment for terminal rigid twin-cube/strict-descent
obstructions, movable hard faces, soft overlap and profile loss,
against true Boolean holes and genuinely unreserved surplus.
A hard face's locally flipped words may still be globally COVERED.
Do not reinterpret such images as holes or assume a false general
subset-Hall principle. The general upper branch, legacy root
compilation and source-closure/prize-eligibility gates remain OPEN.


### Global reverse rigid-face transport and twin-only final debt (2026-10-12)

**Verification boundary:** This work DOES NOT prove or refute JSP-000404,
does not show the lower-branch global payment, and does not close the
upper branch or legacy monolithic Lean root. The research-only
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` retains
**exactly ONE executable `sorry`**, and `#print axioms` honestly
reports `sorryAx`. Its newest obligation is an EXACTLY EQUIVALENT
six-source true-planar net-payment inequality, NOT an established
inequality. The independent `VerifiedOverlapRewire.lean` intentionally
excludes this WIP and has **no imported `sorryAx`**.

**A. Complete retained-incidence twin rigidity.**
`ResidualTerminalRigidTwinIncidence.lean` proves equal-target terminal
rigid carriers have exactly equal incoming AND outgoing retained
colour sets (not just equal completion cubes and active supports):
`incomingRetained(a)=incomingRetained(v)` and
`outgoingRetained(a)=outgoingRetained(v)`.
Successful incremental Lean run
https://github.com/Charlie-Wang-03/awards/actions/runs/38201931381
(no `sorryAx`).

**B. ALL hard carrier edges form a vertex-disjoint matching.**
`ResidualHardCarrierVertexMatching.lean` combines genuine
same-retained-code two-companion uniqueness with a finite ordered
pair matching counting lemma to prove EVERY pair of distinct hard
carriers has disjoint endpoints, independently of their overlapping
Boolean words. Consequently
`2 * card(hardOverlapCarrierPairs C) <= Fintype.card V`,
and specifically
`2 * card(netRigidHardCarriers C k) <= Fintype.card V`.
First CI failed in crossed-endpoint cases because `omega` could not
see order axioms on abstract `V`; repair at
`8b659cca2b5cba236201b1ff96731df2f8532cae` used explicit
strict-order cycles instead. Successful Lean run
https://github.com/Charlie-Wang-03/awards/actions/runs/38202176604
(3,201 tasks, all theorem axioms exclude `sorryAx`).

**C. New REVERSE SAFE-COLOUR for strict-descending terminal rigid
pairs.**
`ResidualTerminalRigidReverseFlip.lean` proves that for a terminal
rigid carrier `a<v` with `k(v)<k(a)`, both one-layer saturated
budgets force `retainedActive(a)\subsetneq retainedActive(v)`.
Since same-retained Boolean codes have equal incoming palettes,
there exists a retained coordinate `c` with
`c in outgoingRetained(v)` and
`c notin retainedActive(a)`.
Flipping ANY word in the entire rigid hard face
`Q_a intersect Q_v = Q_v` at that coordinate sends it into
`Q_a \ Q_v` and into globally singly covered or SOFT overlapping
words. This is the reverse direction of previously proved outward
transport; all images remain COVERED (NOT true Boolean holes).
Successful Lean run
https://github.com/Charlie-Wang-03/awards/actions/runs/38202376520
(3,202 tasks; three theorems no `sorryAx`).

**D. Collision-free GLOBAL reverse whole-face injection.**
`ResidualTerminalStrictReverseGlobalInjection.lean` chooses one such
reverse colour PER strict-descending rigid carrier, independently
of which Boolean word is flipped. The global flip
`netStrictDescentRigidWords -> singletonCompletionWords union
softOverlapCompletionWords` is INJECTIVE: within a face flipping is
involutive, and across distinct carriers the image lies in the
LOWER completion cube of that carrier; verified disjointness of
lower residual centres and same-code carrier matching prevent
collisions. In particular,

`card(netStrictDescentRigidWords) <=
 card(singletonCompletionWords) + card(softOverlapCompletionWords)`.

The existing forward transport and this new reverse transport
are EACH injective. Their IMAGES are **NOT KNOWN TO BE MUTUALLY
DISJOINT** and must NOT be added as two non-reusing sink credits.
Successful Lean run
https://github.com/Charlie-Wang-03/awards/actions/runs/38202600690
(3,203 tasks; no `sorryAx`).

**E. Exact terminal rigid TWO-WAY / net hard THREE-WAY partition.**
`ResidualTerminalTwinStrictPartition.lean` establishes, under the
standard one-layer residual active-card profile budget,

`netRigidHardWords =
 netStrictDescentRigidWords disjoint_union netTwinRigidWords`.

Thus the remaining unpaid hard Boolean words split into
`netTransportableHardWords + netStrictDescentRigidWords
 + netTwinRigidWords` exactly, with no partial faces or repeated
hard-word owners. `netTwinRigidWords` has exact mass
`SUM_(p in netTwinRigidCarriers) 2^k(p.upper)`.
The last TWIN branch requires `k(lower)=k(upper)`,
identical completion cubes and identical incoming/outgoing retained
palettes. It is the sole terminal rigid TYPE not handled by
the two VERIFIED forward/reverse safe-flip mechanisms, NOT the
sole remaining source of the final defect payment.
Successful Lean run
https://github.com/Charlie-Wang-03/awards/actions/runs/38202834492
(3,204 tasks; no `sorryAx`).

**F. Final exact six-source net payment and planar conditional bridge.**
`ResidualTerminalTwinNetPaymentReduction.lean` proves the new
six-source inequality mathematically EQUIVALENT to the preceding
five-source terminal hard net inequality. Independent successful
Lean run https://github.com/Charlie-Wang-03/awards/actions/runs/38202988413
(3,205 tasks).

`PlanarLowerBranchTerminalTwinNetReduction.lean` derives the
one-layer budget from genuine injective planar `AngleCap` geometry
and proves the six-source net-payment hypothesis implies the
lower-branch dyadic capacity. Independent Lean run
https://github.com/Charlie-Wang-03/awards/actions/runs/38203150665
(3,384 tasks; only standard `propext/Classical.choice/Quot.sound`
axioms). At `f8a1e5a15631618af8740bca2bd5b353ec3d9f45`,
the WIP was moved to this precise conditional bridge, keeping the
SOLE admitted `sorry`. WIP run
https://github.com/Charlie-Wang-03/awards/actions/runs/38203307820
(3,385 tasks, PASS with one admitted `sorryAx` as expected).

The ONLY admitted inequality now reads symbolically:

```text
softOverlapMass
+ forwardMovableHardMass
+ reverseStrictDescentRigidHardMass
+ SUM_equalExponentTwinRigid 2^k(upper)
+ SUM_ascendingMixedRigid 2^k(lower)
+ SUM_descendingMixedRigid 2^k(upper)
+ projectedProfileLoss
<= TRUE Boolean holes
 + genuinely UNRESERVED dyadic surplus
   (after paid whole-hard, ascending-lower, descending-upper credits)
```

The exact global **mathematical gap** is to use genuine planar
geometry to pay this inequality WITHOUT reusing previously charged
surplus or reusing singleton/soft covered sinks of the forward and
reverse injections. A possible separate subgoal is proving
sufficient disjointness/multiplicity control of forward/reverse
sink images (collisions could lie in SOFT coverage), then
cross-centre geometric treatment of fully twin rigid pairs.
Do NOT assume arbitrary DirectionData subset Hall or treat covered
singleton/soft images as Boolean holes.

**Full sorry-free Lean umbrella verification:**
`VerifiedOverlapRewire.lean` now imports every new module A-F and
continues to omit admitted WIP. GitHub Actions
https://github.com/Charlie-Wang-03/awards/actions/runs/38203489427
built **3,463 Lean tasks**, with no `sorryAx` introduced into the
independent reduction chain. This is NOT the legacy monolithic root,
nor a completed JSP-000404 proof.


### Opposite-direction covered-sink collision and JOINT capacity (2026-10-12)

**Verified new mathematical step:** The two previously proved
GLOBAL injective transport maps, outward transportable hard faces
and reverse strict-descending terminal rigid hard faces, can be
charged JOINTLY without double counting singleton-covered sinks.
This is a true new cross-map theorem, not a restatement of the
admitted global planar payment.

**Cross collision classification.**
`ResidualForwardReverseSinkCollision.lean` proves that if the
full forward hard transport and the reverse strict-rigid hard
transport send two input words to the SAME Boolean word, that
target is SOFT-OVERLAPPED, never singly covered. The forward
output lies in its residual carrier's UPPER cube Q_v and the
reverse output in a DIFFERENT hard carrier's LOWER cube Q_b;
hard carrier vertex matching shows v != b, hence the output
has at least two distinct completion-fibre owners.
This gives a genuine soft-only collision certificate. The
CI for this module is included in
https://github.com/Charlie-Wang-03/awards/actions/runs/38207178720
and its `#print axioms` excludes `sorryAx`.

**Joint inclusion-exclusion mass bound.**
`ResidualForwardReverseJointSoftMultiplicity.lean` defines
full forward and reverse sink-image Finsets, proves each
cardinality equals its source mass, proves their common image
is a subset of `softOverlapCompletionWords`, and applies
finite-set inclusion-exclusion. Its key unconditional theorem is

```text
card(transportableHardOverlapCompletionWords)
+ card(netStrictDescentRigidWords)
<= card(singletonCompletionWords)
   + 2 * card(softOverlapCompletionWords).
```

In particular, substituting the actually unpaid forward
subfamily and combining exact three-way net-hard partition
and exact twin target mass:

```text
card(remainingUnpaidHardAfterMixedRigidWords)
<= card(singletonCompletionWords)
   + 2 * card(softOverlapCompletionWords)
   + SUM_(twin p) 2^k(p.upper).
```

**The coefficient of singleton covered mass is ONE**, not
the TWO copies obtained by adding old independent bounds.
The remaining coefficient 2 on soft destinations is honest:
a forward and reverse source may collide there; no
inter-map-disjointness is asserted. First CI failed only in the
final `omega` because let-bound singleton/soft Finsets were
not syntactically identified with the original sets. Commit
`08db5de9503b08db7e85076872539a1d5025a778` supplied
explicit let-cardinality equations. Verified PASS:
https://github.com/Charlie-Wang-03/awards/actions/runs/38207178720
(**3,207 Lean tasks**, four theorem `#print axioms` audits
with no `sorryAx`).

**Direction of any surviving cross collision.**
`ResidualForwardReverseCollisionOrder.lean` strengthens the
soft-only classification. Any coinciding forward/reverse sink
words force

```text
reverseLower < forwardUpper
IsResidual C reverseLower forwardUpper
```

because the opposite order would produce a forbidden
monochromatic increasing two-edge path starting with the
forward carrier. This is a concrete oriented residual BRIDGE
which may be paired with genuine planar AngleCap geometry in
later work. It is NOT a contradiction in arbitrary
`OrderedEdgeColoring`, since multiple outgoing colours at
a lower endpoint or multiple incoming colours at an upper
endpoint can coincide. Verified PASS:
https://github.com/Charlie-Wang-03/awards/actions/runs/38207370043
(**3,208 Lean tasks**, both new theorems no `sorryAx`).

**Unresolved mathematical boundary:** the current admitted
`PlanarLowerBranchProofAdmittedWIP.lean` retains exactly ONE
`sorry`, whose net inequality still compares actual TRUE
Boolean holes plus genuinely unreserved dyadic surplus against
soft source mass, both mobile hard masses, twin rigid target debt,
mixed rigid debts and profile loss. None of the new covered-sink
estimates converts a covered singleton or soft word into a
TRUE Boolean hole. Do not cancel the admitted net terms
against the covered image counts. The new joint capacity and
backward bridge identify narrower intermediate geometric
objectives, but they do not prove JSP-000404 or either general
source-closure branch.

The independent `VerifiedOverlapRewire.lean` now imports
all three new no-sorry modules; its full Lean CI is
https://github.com/Charlie-Wang-03/awards/actions/runs/38207499389 .
The WIP remains excluded from this certification umbrella.


### Certified forward/reverse oriented soft-bridge frontier (2026-10-12)

See the standalone auditable handoff:
[BRIDGE_SOFT_PROOF_FRONTIER_2026-10-12.md](BRIDGE_SOFT_PROOF_FRONTIER_2026-10-12.md).

Four new SORRY-FREE Lean files prove unique oriented soft-bridge
ownership of all forward/reverse global transport collisions, joint
capacity `forward + reverse <= singleton + soft + bridgeSoft`,
the exact dyadic formula
`bridgeSoftMass = SUM_bridge 2^card(commonRetainedInactive)`,
and its GENUINE planar `AngleCap` / `centreExponent`
specialization. Each module has independently passing Lean CI;
`VerifiedOverlapRewire.lean` imports them and passes its full
**3,470/3,470** job regression:
https://github.com/Charlie-Wang-03/awards/actions/runs/38209853255 .

The admitted WIP now has the certified genuine-planar auxiliary
`hmobile` in scope, but its sole source-payment `sorry` remains.
WIP 3,392-job CI passes with exactly one expected `sorryAx`:
https://github.com/Charlie-Wang-03/awards/actions/runs/38209708671 .

These new results quantify potential SOFT covered-word collisions
and DO NOT pay TRUE Boolean holes or prove JSP-000404.


### Verified bridge-soft / strict-rigid shared lower-cube capacity (2026-10-12)

Full independent handoff:
[BRIDGE_STRICT_LOWER_GAP_PROOF_FRONTIER_2026-10-12.md](BRIDGE_STRICT_LOWER_GAP_PROOF_FRONTIER_2026-10-12.md).

Four new SORRY-FREE Lean modules:
`ResidualBridgeReverseLowerSharedCapacity.lean`,
`ResidualBridgeReverseLowerDyadicBudget.lean`,
`ResidualBridgeStrictDyadicDescentGap.lean`, and
`PlanarBridgeSoftStrictDyadicGap.lean` establish a certified
shared-capacity refinement of the previous cross-transport bound.

Let `B` be ALL potential SOFT bridge words between reverse
strict-rigid lower and forward transportable upper endpoints;
let `R` be the reverse strict-rigid HARD source face words;
and let `S` be strict-rigid carrier pairs. Then:
```text
B INTER R = EMPTY
B UNION R SUBSET UNION_((b,z) in S) retainedCompletionWords(b)

card(B) + card(R) <= SUM_((b,z) in S) 2^k(b)
card(R) = SUM_((b,z) in S) 2^k(z)
card(B) = SUM_(e in bridgeSoftCarriers) 2^commonInactiveDimension(e)

THUS:
SUM_(e in bridgeSoftCarriers) 2^commonInactiveDimension(e)
 <= SUM_((b,z) in S) 2^k(b) - SUM_((b,z) in S) 2^k(z).
```

The exact lower-cube sum is certified by *pairwise-disjoint*
lower cubes (residual-lower completion uniqueness plus hard vertex
matching) and one-layer double endpoint saturation. A genuine
`AngleCap` / `centreExponent` theorem instantiates this under
the actual planar lower-branch hypotheses. The source gap is
NOT `dyadicProfileSurplus`, because strict rigid endpoints are
individually saturated. Nor are soft or singleton images TRUE
Boolean holes. None of this closes the final six-source global
payment or its one remaining executable `sorry`.

All four modules were individually compiled with standard axioms
only. `VerifiedOverlapRewire.lean` imports them, and the
**3,474 / 3,474** task independent Lean regression PASSED:
https://github.com/Charlie-Wang-03/awards/actions/runs/38216270221 .
The research-only WIP was compiled independently with **3,396**
tasks, one intentional `sorry`/`sorryAx`:
https://github.com/Charlie-Wang-03/awards/actions/runs/38216044106 .


### Certified target-exact matching obstruction (2026-10-14)

`ResidualNetCollisionMatchingObstruction.lean` is included in the
**sorry-free** `VerifiedOverlapRewire` umbrella and imported by the
separate research-only admitted WIP. Four new Lean theorems prove
that two actual same-target NET sources force two candidate exact-shell
edges disjoint on *both* lower and upper original-colour slots. If
each hit target graph contains no such edge pair, actual duplicate
debt vanishes; the genuine mobile ledger then retains only literal
holes, already covered diagonals, and covered singleton/soft words.

This is a *conditional* simplification. No global planar
`AngleCap` matching-exclusion theorem or six-source payment has
been established. The intentionally admitted WIP still contains
one executable `sorry`, and the original JSP-000404 is OPEN.
Module and umbrella validation: [GitHub Actions run 38500726760](https://github.com/Charlie-Wang-03/awards/actions/runs/38500726760),
3,535/3,535 jobs PASS; all four new theorem axiom audits return
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
See [the precise proof-frontier note](BRIDGE_SLOT_MATCHING_OBSTRUCTION_2026-10-14.md).

### Candidate matching graph own-endpoint semantic repair (2026-10-14)

`ResidualNetCollisionExactShellBipartiteCover.lean` now requires
both original-colour slots to be inactive at their own source bridge
endpoints, not merely exact violations at the opposite endpoint.
The actual NET source-to-edge proof uses pre-existing certified
flip-colour inactivity specifications; no real source is excluded.
Every new candidate edge is also certified to project to both
previously verified target-exact endpoint colour-slot pools.
The resulting maximum-matching number counts a smaller, fully
source-compatible candidate graph. This does not pay the remaining
six-source geometric `sorry` or upgrade the result to a full proof.

### Source-native rainbow matching refinement (2026-10-14)

A genuine fixed-target NET source fibre embeds at equal size
into a slot matching with distinct unordered flip-colour supports.
**CORRECTION established by kernel-checked shadow injectivity:**
every pair of DISTINCT candidate edges of the fixed-target graph
already has DISTINCT colour supports. Therefore the maximum
rainbow matching number and ordinary matching number are EQUAL:
`rho(G_d) = nu(G_d)`. The earlier interpretation of a strictly
smaller rainbow capacity was incorrect; the theorem inequalities
remain valid. The proposed colour-clash exclusion is equivalent to
ordinary two-edge matching exclusion in this graph. A truly new
geometric upper bound or non-reused global payment is still missing.

Lean CI: [rainbow capacity 38504690545](https://github.com/Charlie-Wang-03/awards/actions/runs/38504690545)
and [rainbow pair obstruction 38504957833](https://github.com/Charlie-Wang-03/awards/actions/runs/38504957833), both PASS, new
11 theorems free of `sorryAx`. These are honest combinatorial
necessary conditions, not yet a planar AngleCap exclusion or proof
of the unresolved six-source geometric payment.

### Candidate graph → covered soft-shadow injection (2026-10-14)

Two new verified modules formalize a stronger **target-specific** bridge
between Rainbow Matching and ACTUAL covered Boolean words:

- `ResidualNetCollisionCandidateColourVertexSeparation.lean`: two
  candidate exact-shell bridge edges with DISJOINT unordered flip-colour
  supports have all FOUR cross-edge original endpoint incidences distinct.
- `ResidualNetCollisionCandidateShadowCompletion.lean`: for ANY
  candidate edge `((b,cr),(v,cf))`, the double-flip shadow of the fixed
  target `d` lies in BOTH endpoint completion cubes, hence is COVERED.
- `ResidualNetCollisionCandidateShadowInjection.lean`: the original
  bridge is an ordered SOFT overlap carrier. The shadow belongs to
  the actual `softOverlapCompletionWords`, and for a FIXED `d`
  the candidate edge → soft word map is INJECTIVE by unique two-vertex
  ownership and singleton target violation colours. Thus

  `|targetExactShellSlotEdges(C,exponent,d)| <= |softOverlapCompletionWords(C)|`.

The shadow pool is already COVERED. This is NOT a charge to true
Boolean holes and is NOT globally injective across different d.
No geometric matching exclusion, non-reused global dyadic surplus
allocation or closure of the six-source admitted `sorry` is claimed.

CI: [38506236757](https://github.com/Charlie-Wang-03/awards/actions/runs/38506236757)
(PASS 3,541),
[38506654774](https://github.com/Charlie-Wang-03/awards/actions/runs/38506654774)
(PASS 3,542), and
[38507215558](https://github.com/Charlie-Wang-03/awards/actions/runs/38507215558)
(PASS 3,543). One incorrect Lean conjunction projection was
fixed, without changing a mathematical statement.

### Audited exact-shell matching and target-local soft sphere (2026-10-14)

`ResidualNetCollisionRainbowRedundancyAudit.lean` proves
`rho(G_d) = nu(G_d)`; the earlier proposed strict rainbow
capacity improvement did NOT hold for this candidate graph.
[Lean CI 38511850877](https://github.com/Charlie-Wang-03/awards/actions/runs/38511850877):
PASS 3,544, six new theorems without `sorryAx`.

`ResidualNetCollisionLocalSoftSphereCapacity.lean` proves that
every fixed-target candidate edge injects into the ACTUAL SOFT
overlap word set whose Hamming distance from target `d` is exactly
two. This yields a combined pointwise upper bound for the real NET
source fibre by the minimum of the exact-shell ordinary matching
number and the size of this local soft sphere; the exact duplicate
debt/mobile-hard ledger inherit its per-target excess. If each
actually hit target has at most one such soft word, duplicate debt
vanishes (conditional, NOT established under AngleCap).

This local sphere is a subset of COVERED words, NOT a set of true
Boolean holes; no global across-target non-reused charge exists.
The sole admitted six-class planar payment `sorry` remains.
