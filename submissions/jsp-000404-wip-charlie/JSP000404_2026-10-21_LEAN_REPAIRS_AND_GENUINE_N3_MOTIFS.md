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
