# JSP-000404: targeted Lean repairs and genuine five-centre geometry checkpoint

Date: 2026-10-21. Research branch: `research/jsp-000404-sharp-centre`.

## Scope and trust boundary

This is **not** a complete proof of JSP-000404. The original planar lower-branch WIP theorem in
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` still has its single intentionally admitted
global geometric-payment subgoal, and `#print axioms` on that WIP headline necessarily includes
`sorryAx`. The unproved issue is a **global, non-reusing, original-vertex-level six-source payment**
compatible with the dyadic capacity. In particular, a slot matching alone is not such a payment.

The earlier closed `n=1`, `n=2` and at-most-four-centre branches remain separate from this WIP.

## Five repaired source modules: focused kernel verification

| Module | Principal repair | Successful Actions run |
|---|---|---|
| `CutBandSmallAngle.lean` | eliminate shadowed lambda binder in real cut-band angle theorem | [39586724094](https://github.com/Charlie-Wang-03/awards/actions/runs/39586724094) |
| `CutCentreTransitionPath.lean` | lambda binder correction and `noncomputable` real path gaps | [39586819191](https://github.com/Charlie-Wang-03/awards/actions/runs/39586819191) |
| `ResidualChildMass.lean` | classical finite residual subtype instances, subtype sum identifications, power identity | [39587015815](https://github.com/Charlie-Wang-03/awards/actions/runs/39587015815) |
| `ConcreteCentreDeletionGain.lean` | `Nat.one_le_floor_iff` lifts floor evidence to actual real-angle gap bounds | [39587450471](https://github.com/Charlie-Wang-03/awards/actions/runs/39587450471) |
| `CutNormalizedPhase.lean` | unfold actual phase and cut-ray definitions, not absent helper names | [39588576640](https://github.com/Charlie-Wang-03/awards/actions/runs/39588576640) |

Each successful focused build prints the source module's theorem axioms without `sorryAx`.
This does **not** assert a successful full-tree build; other pre-existing modules in the full-tree
incremental workflow continue to require separate repair.

## Two additional certified modules

### `ThreeFiveNoTopWeight.lean`

Focused success: [39587694579](https://github.com/Charlie-Wang-03/awards/actions/runs/39587694579).

- `zero_one_dyadic_sum_eq_card_add_ones`
- `five_centre_no_top_overweight_forces_four_next`
- `five_centre_no_top_at_most_three_next_capacity`

For five vertices and exponents `k(i) <= 1`, the mass is exactly
`sum_i 2^k(i) = 5 + #{i | k(i) = 1}`. Hence mass `>8` requires at least four
exponent-one vertices. These are pure finite arithmetic statements and are no substitute
for a planar exclusion theorem.

### `ThreeFiveOverweightPlanarMotifs.lean`

Focused success: [39589148617](https://github.com/Charlie-Wang-03/awards/actions/runs/39589148617).
`lake build JSP000404Research.ThreeFiveOverweightPlanarMotifs` succeeded (3502 jobs).
`#print axioms JSP000404Research.planar_three_five_overweight_profile_dichotomy`
reports precisely `[propext, Classical.choice, Quot.sound]` and **no `sorryAx`**.

This is a theorem on **actual injective planar points**, an actual
`AngleCap p lam`, `0 <= delta < 1/2`, `t = 3 + delta`,
`lam = pi/t`, exactly five centres and their genuine `CentreProjectiveCycle` data.

It proves the following necessary dichotomy for any mass violation `sum_i 2^k(i) > 8`:

1. **No top:** all `k(i) <= 1`, with at least four centres of exponent `1`;
2. **Top + unique next:** one centre of exponent `2` and exactly one centre
   of exponent `1` (the uniqueness is deduced geometrically from the
   existing top/next multiplicity exclusion).

**Neither motif is excluded by this theorem.** The result converts an
arbitrary five-centre `n=3` overweight scenario into two sharp geometric
subtasks but does not establish `sum_i 2^k(i) <= 8`.

## Exact next mathematical obligations

- Prove the no-top / at-least-four-next motif impossible under actual `AngleCap`,
  or derive its compensation through a certified source allocation.
- Prove the top-plus-unique-next five-centre overweight motif impossible,
  or provide an independent geometric compensation.
- Generalize the original-vertex non-reuse payment argument to all
  `n >= 3` and at least five original centres; the two `n=3` motifs alone
  do not close the full theorem.
- Perform a fresh full-tree build-error census; focused PASS is not full-tree PASS.
- Keep the original published-source / mathematical closure gate separate from kernel checks.

## External priority evidence: statement correspondence cautions

A focused inspection on 2026-10-21 found that
[upstream PR #2751](https://github.com/TheJustinSunPrize/awards/pull/2751)
cites an `ErdosProblems/Erdos404.lean` for **Erdős Problem #404**, not the
JSP-000404 / Blumenthal–Sendov problem associated with **Erdős #504**.
Name similarity is not a statement match.

[Upstream PR #2804](https://github.com/TheJustinSunPrize/awards/pull/2804)
cites `Yi-111-a/jsp-000404-blumenthal-sendov` at pinned commit
`f7bf2cce3bd37fec9f1bce2d04c47b8b88c88061`. Its
`lean/JSP404/Defs.lean` **defines** `alpha N` as the target Sendov
piecewise formula, and `Main.lean` checks the formula by unfolding that
definition and computing `Nat.clog`. This does not, on its face,
prove equality with the planar configuration extremum from its original
geometric definition. This limited finding is not a comprehensive audit
of all JSP-000404 submissions and does not assert competitive priority.

## Policy

No new axioms, no added `sorry`, no mathematical solver or complete-formalization
credit claim, and no upstream submission of the incomplete original theorem.


## Follow-up: exact profile equivalence and verified historical repairs

New Lean source changes on the same research branch, verified by dedicated GitHub
Actions on 2026-10-21:

| Scope | Lean file / fully qualified theorem | Status and evidence |
|---|---|---|
| Geometry-to-Hansel one-extra-band capacity | `ProjectiveBandOneLayerCapacity.lean`: `projectiveBand_oneLayer_capacity` | [focused success #39592787355](https://github.com/Charlie-Wang-03/awards/actions/runs/39592787355) |
| Concrete deletion exponent monotonicity | `ConcreteCentreDeletionMonotone.lean`: `centreExponent_mono_restrictDelete`, plus seven related deletion lemmas | [focused success #39593267711](https://github.com/Charlie-Wang-03/awards/actions/runs/39593267711), 3232 build jobs; all eight audited declarations without `sorryAx` |
| Exact n=3 five-centre obstruction *iff* | `ThreeFiveExactOverweightEquivalence.lean`: `ternary_dyadic_sum_exact`, `planar_three_five_dyadic_mass_exact`, `planar_three_five_overweight_iff_two_motifs` | [focused success #39593612361](https://github.com/Charlie-Wang-03/awards/actions/runs/39593612361), 3503 build jobs; all three declarations only `[propext, Classical.choice, Quot.sound]` |
| Arbitrarily rotated projective-cut ray cycle | `CutCentreRayCycle.lean`: `exists_centreCutRayCycle`, `CentreCutRayCycle.get_rayIndex`, `CentreCutRayCycle.cutTheta_le_of_rayIndex_le` | [focused success #39594239731](https://github.com/Charlie-Wang-03/awards/actions/runs/39594239731), 3237 build jobs; no `sorryAx` in these three declarations |

### Mathematical status of the exact equivalence

For the actual five-centre planar setup with `n=3`, `0 <= delta < 1/2`,
`t=3+delta`, `lam=pi/t` and the genuine `AngleCap`, write
`k(i)=centreExponent (C i) t`. The new kernel-checked identity is

`sum_i 2^k(i) = 5 + #{i : k(i)=1} + 3 * #{i : k(i)=2}`.

The actual geometric top-layer rigidity from earlier certified modules
then yields the **logical equivalence**:

`sum_i 2^k(i) > 8` if and only if either

* **A (no top):** `forall i, k(i)<=1` and at least four `k(i)=1`; or
* **B (top and next):** one `k(s)=2` and exactly one `k(a)=1`.

There are **no added profile assumptions in the theorem**: all cases are
directly quantified over the genuine planar AngleCap centre cycles.
Neither A nor B has been geometrically ruled out. Hence the theorem
does not prove `sum_i 2^k(i) <= 8`, and it is not a proof of the
full JSP-000404 classification.

The one-extra-band theorem establishes the weaker genuine global bound
`sum_i 2^k(i) <= 2^(n+1)`; it does not pay for the extra band.
Concrete centre deletion monotonicity provides `k_parent <= k_child`
at surviving centres and therefore does not alone control the aggregate
potential. The rotated-cut ray cycle is an auxiliary geometric transport
tool, not the missing globally non-reusing six-source allocation.

### Remaining proof and build obligations

1. Geometrically exclude both exact A and B motifs (or supply a sound
   non-reusing capacity payment for them) to close `n=3`, five centres.
2. Close the global non-reusing six-source payment for arbitrary
   `n>=3` and at least five centres; the WIP headline in
   `PlanarLowerBranchProofAdmittedWIP.lean` retains exactly one deliberate
   `sorry` and thus depends on `sorryAx`.
3. Continue repairing other historical modules from the repository's
   fast-incremental full-target compile: independently successful focused
   CI does **not** imply the entire research module graph passes.
4. Keep upstream prize submission and full-proof authorship claims
   gated on statement equivalence, mathematical closure, complete build,
   and a `#print axioms` free of `sorryAx`.

No upstream PR was opened by this follow-up, and no new axiom or proof
admission was introduced.


## Second continuation: both n=3 motif support constraints and cut-cycle compiler closure

Verification is through the linked **completed successful** dedicated GitHub
Actions. All source files are on `research/jsp-000404-sharp-centre`.

| Deliverable | Proof/Lean meaning | Verification |
|---|---|---|
| `ExplicitCutRayCycle.lean` | Repairs historical missing List permutation and length-zero lemmas; constructs a canonical projective-cut sorted ray cycle with explicit retained `low ++ high` split | [CI #39605503450 — SUCCESS](https://github.com/Charlie-Wang-03/awards/actions/runs/39605503450), 3,238 Lake jobs, both audited declarations without `sorryAx` |
| `CutLocalBandCycle.lean` | Repairs noncomputable declarations, `List.Perm` membership, normalized-angle arithmetic, and implicit centre; proves `CentreCutRayCycle.exponent_eq_centreExponent`: actual canonical centre exponent is invariant under changing the projective cut | [CI #39607077023 — SUCCESS](https://github.com/Charlie-Wang-03/awards/actions/runs/39607077023), 8,973 Lake jobs, three audited declarations without `sorryAx` |
| `TopNextSupportOneFourCentrePacking.lean` | NEW geometry: `no_top_next_support_one_with_two_low_support_companions` and `top_next_support_one_low_support_card_le_one` | [CI #39605740503 — SUCCESS](https://github.com/Charlie-Wang-03/awards/actions/runs/39605740503), 3,449 Lake jobs, only `propext`, `Classical.choice`, `Quot.sound` |
| `NoTopNextLayerFourCentrePacking.lean` | NEW geometry: `no_three_next_support_one_with_fourth_low_support` and its unconditional next-layer consequence `no_three_support_one_among_four_second_layer_centres` | [CI #39607838427 — SUCCESS](https://github.com/Charlie-Wang-03/awards/actions/runs/39607838427), 3,499 Lake jobs, both declarations without `sorryAx` |

### New geometric necessary conditions in the first unresolved n=3, five-centre case

Let `k_i = centreExponent (C i) t`, with `t=3+delta`,
`0<=delta<1/2`, `lam=pi/t`, and genuine planar `AngleCap`.

The previously certified exact equivalence
`sum_i 2^k_i > 8 <=> A or B` remains valid.

* **A: no exponent-2 centre, at least four exponent-1 centres.**
  The new theorem proves no four *distinct exponent-1 centres* can
  include three with quotient positive support one. The previously
  kernel-checked deficit-two support classification says such
  exponent-1 centres have positive support either one or two.
  **Therefore at least two of any four exponent-1 centres in A
  have positive support exactly two.** This is a necessary condition,
  not yet an exclusion of A.
* **B: one exponent-2 centre and exactly one exponent-1 centre.**
  If the unique exponent-1 centre has positive support one,
  the new cardinal theorem proves that at most ONE of the other
  original centres can have positive support at most two.
  For exactly five centres, at least TWO of the three lower-exponent
  centres must therefore have positive support at least three.
  The alternative where the unique exponent-1 centre has
  positive support two is **not removed** by this theorem;
  B remains open.

These use the genuine global transition-quotient packing
`sum cert.qe <= 2*n`, not an assumed or fictional payment.
The four-centre contradictions are `n+(n-1)+1+1>2*n`
(top-next support-one) and `3(n-1)+1>2*n`
(three next-layer support-one), respectively.

### Honest unresolved gates

The two exact planar n=3 five-centre configurations A and B are
NOT fully excluded. Arbitrary n>=3/card>=5 global source-unique
six-source payment, exact true Boolean holes, nonreserved slack,
NET duplicates, fifth-centre/twin/mixed/soft debts remain OPEN.
The principal `PlanarLowerBranchProofAdmittedWIP.lean` still has
its original deliberate one `sorry` (`sorryAx` in the headline).
The full historical research module graph still has other compilation
errors. Success of the **focused** jobs is not full-tree acceptance.
No added axiom, no new proof admission, and no upstream submission.


## Third continuation: targeted historical repairs and an actual four-centre support-two certificate

This continuation is deliberately scoped to source repairs and a genuine geometric **necessary condition**. It is **not** closure of the full JSP-000404 theorem.

### Kernel-checked outcomes

- `ConcreteMinimumOverweightRigidity.lean`: fixed two dependent `match` eliminations by explicit cases on deleted-ray prefix and suffix lists. Focused [Actions #39610641661](https://github.com/Charlie-Wang-03/awards/actions/runs/39610641661) **SUCCESS**; `lake build JSP000404Research.ConcreteMinimumOverweightRigidity`, 3519 jobs.
- **New** `NoTopNextLayerTwoSupportTwo.lean`: `JSP000404Research.two_support_two_among_four_second_layer_centres`, focused [Actions #39611067539](https://github.com/Charlie-Wang-03/awards/actions/runs/39611067539) **SUCCESS**, 3500 Lake jobs. `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`, not `sorryAx`.

For four *distinct actual planar* centres of exponent `n-2`, their quotient positive support is in `{1,2}`. The existing real `AngleCap` four-centre transition-packing theorem excludes every triple with support one. By exhaustive disjunction, **at least two of the four necessarily have support two**. This refines the no-top / four-next (`n=3`, five-centre) overweight motif; it does NOT exclude it.

### Compiler-repair and verification status

- Removed five nonexistent `Mathlib.Data.Matrix.Notation` imports, without changing theorem statements: commit `ec94c907d7f616a03754e8da2d7376f00403a1a8`.
- Repaired the historically broken sharp support-three deletion-gain module's missing `ConcreteMaxStableCentre` import, `prefix` identifier, shadowed `lam` binder, and two list-rotation goals. Dedicated workflow: `jsp000404-focused-sharp-support-three-deletion-gain.yml`. A final successful focused kernel check is required before recording this repair as accepted.
- Reordered shadowed `lam` binders in `CutSaturatedEndpointDichotomy.lean` (eight theorem sites) and `ExactWitnessShortArc.lean` (three theorem sites), and subsequently repaired two exact-short-arc local proof obligations. Dedicated focused workflows are the acceptance gates; unverified source edits are not counted as verified mathematical closure.
- Full-target incremental compilation has numerous **independent historical errors**; no full-tree PASS is claimed.

### Remaining proof obligations (unchanged full-scope gate)

1. Exclude both actual five-centre `n=3` overweight motifs, including the no-top four-next profile **with at least two support-two centres** and the top-plus-unique-next profile.
2. Establish the original-vertex-level, globally non-reusing six-source net-payment inequality for every `n>=3` and at least five original centres, accounting separately for true Boolean holes, NET duplicate debt, already reserved dyadic mass, mixed rigid debts and equal-exponent twin rigid debt.
3. Produce full source-graph Lean build, theorem correspondence audit, and an axiom audit free of `sorryAx` **before** any claim of complete formalization.

The main `PlanarLowerBranchProofAdmittedWIP.lean` still contains the same single admitted `sorry`. No upstream complete-proof submission or prize claim has been made in this continuation.


### Follow-up verified kernel certificates

Two historically noncompiling geometry modules have now reached independently successful focused builds:

- `JSP000404Research.sharp_support_three_delete_sharp_gain` in `SharpSupportThreeDeletionGain.lean`: [Actions #39612859159](https://github.com/Charlie-Wang-03/awards/actions/runs/39612859159), **SUCCESS**, 3523 Lake jobs. The theorem's audited axioms are exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. The completed code includes import, binder, list-append, list-rotation, and identifier repairs.
- `ExactWitnessShortArc.lean`: [Actions #39612971496](https://github.com/Charlie-Wang-03/awards/actions/runs/39612971496), **SUCCESS**, 3229 Lake jobs. The corrected ordinary/wrap projective short-arc conclusions use actual ray-angle nonnegativity; the audited local declarations do not rely on `sorryAx`.

These results do not change the principal WIP theorem's single admitted six-source payment or certify the full module tree.


## Fourth continuation: five-centre transition obstruction and cut-saturation repair (2026-10-21)

### Certified successes

- **CutSaturatedEndpointDichotomy.lean**: [focused CI #39616691044](https://github.com/Charlie-Wang-03/awards/actions/runs/39616691044) **SUCCESS**; 8,976 Lake jobs, its three printed declarations have no `sorryAx`. The previously failing file required fixes to `lam` binder order, actual centre-cycle arguments, normalization/floor witness rewrites, dependent list splitting, and the precise `List.getLastD_eq_getLast?` theorem.
- **ThreeFiveTopLowSupportPacking.lean**: [focused CI #39616347027](https://github.com/Charlie-Wang-03/awards/actions/runs/39616347027) **SUCCESS**; 3,500 Lake jobs. The new theorems `no_top_three_with_four_low_support` and `top_next_three_companions_one_support_ge_three` both report exactly `[propext, Classical.choice, Quot.sound]`, without `sorryAx`.

The second theorem is a **genuine planar** restriction on the n=3, five-centre top-plus-next overweight motif B. For one true exponent-2 top centre and one true exponent-1 next centre, at least one of the other three distinct centres has positive quotient support >=3. Why: a genuine top transition costs exactly 3 units, each further support<=2 centre has a positive transition certificate, and the proved packing total is <=6; 3+4>6. The next exponent-1 centre automatically has support<=2, so all three remaining low centres cannot also have support<=2.

This **does not** geometrically exclude B, prove the five-centre capacity, or pay the full six-source debt.

### Unverified continuation and environment incidents

- `ThreeFiveSupportThreeRigidity.lean` is a newly submitted follow-on: from `sum(q)<=3` and `centreExponent + positiveSupport = sum(q)`, support>=3 should yield exact support 3, exponent 0 and sum(q)=3. The corollary applies this to one of the other three B-companion centres. These are **pending focused Lean acceptance**, not counted as certified here.
- `SupportTwoNarrowClusters.lean` has been revised to restore local list-alignment, support-count, and all-zero gap-mass lemmas. The initial [focused run #39617025832](https://github.com/Charlie-Wang-03/awards/actions/runs/39617025832) failed at `lake exe cache get` due to runner DNS resolution of `release.lean-lang.org`, before source compilation; the failed job was rerun. No mathematical/Lean success is inferred from an infrastructure failure.

### Global closure gate

The full original lower-branch theorem **still has one intentional executable `sorry`** in `PlanarLowerBranchProofAdmittedWIP.lean`; it still depends on `sorryAx`. The globally source-unique six-source payment for arbitrary n and original-centre cardinality remains open. Focused successful modules are not an all-tree build or a solution of JSP-000404.


### Fourth continuation: exact n=3 high-support profile — verified

`ThreeFiveSupportThreeRigidity.lean` passed [dedicated CI #39617482643](https://github.com/Charlie-Wang-03/awards/actions/runs/39617482643), 3,501 Lake jobs. Both `three_scale_high_support_exact_rigidity` and `top_next_three_exact_support_three_companion` have the ordinary kernel axioms `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

For any genuine centre at `t=3+delta`, `0<=delta<1/2`, the certified quotient sum bound is `sum(q)<=3`, and `sum(q)=centreExponent+positiveSupport`. Therefore `positiveSupport>=3` implies the **exact** equalities:

```text
centreExponent = 0
positiveSupport = 3
sum(quotients) = 3
```

Applied to the genuine five-centre top-plus-next motif B (one exponent-2 centre, one exponent-1 centre), at least one of the three remaining original centres has that exact profile. This is a structural **necessary condition**, not a planar exclusion, and not full dyadic capacity.

`ThreeFiveCompanionUnitQuotients.lean` has also been submitted as a separate proof obligation: zero floor excess forces each quotient <=1, implying the candidate companion has exactly three unit-positive quotient entries. Its focused CI outcome must be checked separately before promotion to certified.

The only admitted WIP headline still contains its exact one executable `sorry`; all source-unique global payments remain open.


### Fourth continuation: restored two-narrow-cluster list proof (verified)

`SupportTwoNarrowClusters.lean` passed dedicated [CI #39618261703](https://github.com/Charlie-Wang-03/awards/actions/runs/39618261703): `lake build JSP000404Research.SupportTwoNarrowClusters`, **3,445 Lake jobs, SUCCESS**. `#print axioms` on `split_unique_positive_of_count_one`, `listZeroGapMass_two_zero_blocks` and `exists_two_narrow_zero_blocks` returned `[propext, Classical.choice, Quot.sound]` without `sorryAx`.

The restoration explicitly proves finite-list append support identities, zero-positive-support quotient sums, and zero-quotient aligned gap mass, then completes the previously invalid indexed induction and its conditional simplification. The earlier DNS failure during `lake exe cache get` was an infrastructure problem, distinct from the subsequently repaired two Lean source errors.

No all-tree PASS is implied. The unique principal global `sorry` remains as recorded above.


### Fourth continuation: three unit-positive quotients in an actual n=3 B-companion — VERIFIED

`ThreeFiveCompanionUnitQuotients.lean` passed [focused CI #39618465324](https://github.com/Charlie-Wang-03/awards/actions/runs/39618465324), 3,502 Lake jobs. All three printed theorem axiom reports are exactly `[propext, Classical.choice, Quot.sound]` and do **not** contain `sorryAx`.

The proof adds the integer statement `floorExcess q = 0 -> forall i, q(i) <= 1`, using a nonnegative summand bound and the definition of `floorExcess`. Together with the previous verified five-centre top-plus-next transition packing and support-three rigidity, **at least one of the other three actual original centres** in the n=3 B-motif has all of:

- `centreExponent = 0`;
- `positiveSupport = 3`;
- `sum(centreQuotient) = 3`;
- `forall r, centreQuotient(r) <= 1`.

Consequently its positive integer quotient entries are **exactly three unit entries**, while the remaining entries are zero. This narrows the genuine geometric profile B but does not demonstrate its impossibility. Source-level cardinality exactly five yields four non-centre rays; a no-top original-centre exclusion and the globally non-reusing six-source payment are still absent.

The WIP main theorem still has the same one admitted `sorry` at `PlanarLowerBranchProofAdmittedWIP.lean:900`, not closed by this local certificate.


## Fifth continuation: zero-gap slack and historical module compile restoration (2026-10-21)

### Verified Lean kernel certificates

- `SupportThreeZeroAngleBlocks.lean`: [CI #39629572024](https://github.com/Charlie-Wang-03/awards/actions/runs/39629572024), **SUCCESS**, 3,451 Lake jobs. Four previously failing Lean elaborations were repaired: nonexistent `List.length_eq_zero.mp`, a list-recursive `simp`, and the list-length arithmetic missing `congrArg List.length hsplit`. The four named `#print axioms` results exclude `sorryAx`.
- `ZeroExponentMinimalDeletionRigidity.lean`: [CI #39629571906](https://github.com/Charlie-Wang-03/awards/actions/runs/39629571906), **SUCCESS**, 3,589 Lake jobs. Removed two invalid extra tactic branches after the goals had already been solved. Its three printed declarations use no `sorryAx`.
- `ThreeScaleZeroGapSlack.lean` (first two theorems): [CI #39630320897](https://github.com/Charlie-Wang-03/awards/actions/runs/39630320897), **SUCCESS**, 3,503 Lake jobs. Exact finite-floor remainder identity: for `t=3+delta`, unit-sum nonnegative normalized gaps and quotient sum three, `sum_r(t*g_r-floor(t*g_r))=delta`. Hence each true zero quotient gap has `t*g_r<=delta`. Combined with the previously verified exact support-three rigidity, this holds for an actual planar centre at the n=3 five-centre top-plus-next motif B. The corresponding new direct five-centre existential corollary has been submitted in the same module; **its own later CI result is independently required**.

### Repairs still requiring their own acceptance

- `TransitionGapRayAlignment.lean`: an actual source-graph duplicate declaration `successiveDiffsFrom_append_cons` was renamed to `transitionRay_successiveDiffsFrom_append_cons`; this avoids collision with the already defined theorem in `ProjectiveCutRotation.lean`. Dedicated composite-import check `CutSupportInvariant` revealed further unrelated historical source errors, not a residual duplicate-name error.
- `CutSupportInvariant.lean`: candidate repairs for list cyclic permutation, pairwise map transport, an empty-list length witness and an append-nil witness; pending kernel retest.
- `CutQuotientRotation.lean`: corrected unsupported `~` permutation syntax to explicit `List.Perm`, and candidate follow-on fixes to permutation, sorted transport, and cut-list cases; pending kernel retest.

### Strict outstanding goal

The main `PlanarLowerBranchProofAdmittedWIP.lean` still retains its one explicit `sorry` at line 900. This is the globally source-unique six-source NET debt payment (true Boolean holes, no reuse of reserved dyadic slack, original-vertex NET duplicate debt, covered/mixed/soft/rigid/twin debts) and **is not discharged** by zero-gap angular slack or focused build repair. Exact planar n=3 five-centre motifs A and B are still not excluded; full module graph build still fails independently on historical files. These modules are research, not a complete proof submission.


### Fifth continuation: direct B-profile narrow-gap corollary VERIFIED

Following the first zero-gap slack certificate, the strengthened direct five-centre theorem
`top_next_three_has_narrow_unit_gap_companion` passed [CI #39630941142](https://github.com/Charlie-Wang-03/awards/actions/runs/39630941142), 3,503 Lake jobs, `#print axioms` without `sorryAx`.

For five *distinct actual planar centres* with an exponent-2 top and exponent-1 next centre at `n=3`, some one of the other three genuine centres has simultaneously
`positiveSupport(q)=3`, `forall r, q(r)<=1`, and
`forall r, q(r)=0 -> t*g(r)<=delta`.
Since the support is three and every positive quotient equals one, this is an exact three-unit-quotient centre with every zero quotient angular gap bounded by `delta/t` when `t>0`.

The statement is only a **necessary profile for unresolved B**, not a contradiction, and does not close the five-centre global dyadic capacity.

### Fifth continuation: continuing historical compile repairs

Changes additionally repair/attempt compile gates for `CutSupportInvariant.lean`, `CutQuotientRotation.lean`, `MixedSupportTransitionCeiling.lean`, and `ThirdLayerSupportOneMultiplicity.lean`. Each requires its own later focused CI success before being described as certified. All are orthogonal to the WIP's single remaining global `sorry`.


### Fifth continuation: independently certified cut-rotation modules

- `CutQuotientRotation.lean`: [CI #39632494161](https://github.com/Charlie-Wang-03/awards/actions/runs/39632494161), **SUCCESS**, 8,974 Lake jobs. The full canonical-to-cut quotient permutation bridge is restored; the three printed axioms exclude `sorryAx`.
- `CutSupportInvariant.lean`: [CI #39632556417](https://github.com/Charlie-Wang-03/awards/actions/runs/39632556417), **SUCCESS**, 8,985 Lake jobs. The cut-independent positive-support list rotation and its dependent sorted-ray transport now compile. These fixes also remove the formerly conflicting duplicate gap-split identifier from the import graph.

The separate n>=5 six-point `MixedSupportTransitionCeiling.lean` and `ThirdLayerSupportOneMultiplicity.lean` require focused acceptance after fixing dependent three-centre certificate vectors and their quotient-sum projection; the last commit does **not** independently certify them.

This restores historical invariants, not the original global six-source `sorry`.


### Fifth continuation: profile A exact next-layer quotient rigidity — candidate

New `ThreeFiveNextSupportTwoRigidity.lean` introduces `exponent_one_support_two_exact_mass`: at an exponent-one next-layer centre, positive support two forces **quotient sum three** and `forall r, quotient(r)<=2` by the exact floor-excess plus support identity. This is elementary local arithmetic, not an additional geometry hypothesis.

The second theorem, `two_saturated_next_among_four_n3`, applies the previously kernel-checked genuine four-centre transition-packing restriction: in the n=3 no-top four-next motif A, among any four distinct actual exponent-one centres at least two have the exact (exponent 1, support 2, quotient sum 3, quotient entries <=2) profile. Its new focused [CI #39632912015](https://github.com/Charlie-Wang-03/awards/actions/runs/39632912015) is the acceptance gate. This statement is **not marked verified until CI succeeds**, and does not exclude A.

Current historical source improvements include extra dependent `Fin 3` certificate-function elaboration fixes for `MixedSupportTransitionCeiling` and `ThirdLayerSupportOneMultiplicity`. The large original global source payment remains admitted once in the WIP root.


### Fifth continuation: profile A certificate and six-point support-one rigidity ACCEPTED

- `ThreeFiveNextSupportTwoRigidity.lean`: [CI #39632912015](https://github.com/Charlie-Wang-03/awards/actions/runs/39632912015), **SUCCESS**, 3,501 Lake jobs. All three theorem axiom reports contain precisely `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. Applying real planar `AngleCap` quartet transition packing and the elementary `floorExcess+positiveSupport=sum(q)` identity, in the genuine n=3 motif A at least two distinct exponent-one next-layer centres have `positiveSupport=2`, `sum(q)=3`, and `forall r, q(r)<=2`, hence integer positive quotient multiset {1,2}. This is a necessary condition, NOT impossibility of A.
- `ThirdLayerSupportOneMultiplicity.lean`: [CI #39633031649](https://github.com/Charlie-Wang-03/awards/actions/runs/39633031649), **SUCCESS**, 3,448 Lake jobs. The restored `no_top_with_two_support_one_deficit_three` theorem is printed with `[propext, Classical.choice, Quot.sound]` only. This conditional n>=5 third-layer obstruction was repaired by explicit dependent Fin 3 family/certificate indexing and certificate-quotient projection; it is NOT the global six-source payment theorem.

`MixedSupportTransitionCeiling.lean` has received the analogous dependent-family and projection repairs; independent acceptance still must be read from its focused run. The entire source graph is not claimed to compile and the principal WIP still retains its one admitted `sorry`.


### Fifth continuation: mixed support transition ceiling ACCEPTED

`MixedSupportTransitionCeiling.lean`: [focused CI #39633102373](https://github.com/Charlie-Wang-03/awards/actions/runs/39633102373), **SUCCESS**, 3,498 Lake jobs. `transition_qe_le_two_beside_top_and_support_one` has the ordinary kernel axioms `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. Its actual result is conditional: in the n>=5 profile with one n-1 top centre and a distinct support-one n-3 centre, any third distinct centre's transition-certificate quotient is at most two. This is a genuine local transition ceiling, not arbitrary-cardinality source-unique payment.

Compilation was recovered by binder ordering, explicit dependent `Fin 3` families/certificates, and pointwise certificate quotient equality before arithmetic projection.

### Explicit remaining top-level blockers

1. Neither n=3, five-centre overweight motif A nor B has a proved geometric contradiction. The new exact-quotient and narrow-angle necessary conditions restrict them.
2. The primary lower-branch theorem retains the **one executable `sorry`** in `PlanarLowerBranchProofAdmittedWIP.lean:900`, representing the original-source-disjoint global six-source NET debt payment for arbitrary n and >=5 original centres.
3. The broad historical research module graph remains subject to other independent compilation errors. A collection of focused successful Lake targets is not a full-tree success, and no upstream complete-proof assertion has been made.


## 2026-10-22 continuation: five-centre angular mass and six-point ledger

### Kernel-checked in this continuation

| Lean module | Focused GitHub Actions | Results | Axiom condition |
|---|---|---|---|
| `SixPointSupportMultiplicityReduction.lean` | [#39641998656](https://github.com/Charlie-Wang-03/awards/actions/runs/39641998656) | **PASS**, 3,452 Lake jobs | no `sorryAx` |
| `ThreeFiveNoTopNarrowZeroGaps.lean` | [#39642407423](https://github.com/Charlie-Wang-03/awards/actions/runs/39642407423) | **PASS**, 3,506 jobs | no `sorryAx` |
| `CutActiveFloorEquiv.lean` | [#39643251956](https://github.com/Charlie-Wang-03/awards/actions/runs/39643251956) | **PASS**, 8,977 jobs | no `sorryAx` |
| `SharpSupportThreeTwoClusters.lean` | [#39643449196](https://github.com/Charlie-Wang-03/awards/actions/runs/39643449196) | **PASS**, 3,461 jobs | no `sorryAx` |
| `SixPointTopDeletionWeight.lean` | [#39643449236](https://github.com/Charlie-Wang-03/awards/actions/runs/39643449236) | **PASS**, 3,524 jobs | no `sorryAx` |
| `ThreeScaleZeroGapAggregateBudget.lean` | [#39643593257](https://github.com/Charlie-Wang-03/awards/actions/runs/39643593257) | **PASS**, 3,507 jobs | no `sorryAx` |
| `ProjectiveBandLastMergeCapacity.lean` | [#39643764365](https://github.com/Charlie-Wang-03/awards/actions/runs/39643764365) | **PASS**, 8,960 jobs | no `sorryAx` |

**Mathematical content.** At `n=3` and `t=3+delta`, in the actual planar five-centre no-top motif A, among any four genuine exponent-one next-layer centres at least two have:
- exact positive quotient support two, integer quotient mass three and every integer quotient at most two (thus two positive quotients `{1,2}`);
- every zero-floor gap `r` satisfies `t*g_r<=delta` (proved using the actual `CentreProjectiveCycle`).
Further, for *any subset of zero-floor gaps at such a saturated centre*, the **sum** of their scaled widths is `<=delta`, not `delta` separately per gap. This is the strict local **one-remainder, no duplicate angular credit** principle; it does not pay other original-vertex NET debts.

The sharp-centre conditional support-three two-zero-angle-block lemma is also kernel-checked: the two surviving zero-quotient actual-angle blocks together have mass `<=delta*lam`. The conditional `n+1 -> n` projective-band last-colour merge capacity theorem was restored, but requires a real wrap bit and saturation-boundary conditions; it is not a standalone universal planar solution.

**Other repaired interfaces.** `CutActiveFloorEquiv` now uses correct `CentreCutRayCycle` namespace, original centre cycle `C`, and explicit cut witness `R`. `SixPointSupportMultiplicityReduction` uses current Mathlib Finset subset-cardinality and pair-existence lemmas. `SixPointTopDeletionWeight` uses checked natural-number dyadic arithmetic and a corrected finset sum decomposition. `ProjectiveBandLastMergeCapacity` resolves Lean `Fin n` zero construction, pairwise active colour image equality, and the proof-irrelevant projective-band instantiation.

### Pending acceptance and principal open gap

- `GeneralSaturatedZeroGapBudget.lean` generalizes the aggregate angular-budget proposition to arbitrary `n` for any exponent-`n-3`, support-three centre. It remains **unverified until its own focused CI and axiom audit pass**.
- The fast full incremental check at the previous branch head reported **241 historical Lean diagnostics in 24 files**. That is not a full-tree compilation PASS; several more focused modules are now repaired, but a fresh completed full-tree error count is needed.
- `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` still has exactly its deliberately retained global source-nonreusing six-source NET payment `sorry` at line 900. No theorem in this continuation justifies removing it. Both true five-centre overweight motifs A and B remain geometrically unexcluded.
