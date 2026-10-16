# JSP-000404 — Lean repair and conditional-capacity checkpoint

Date: 2026-10-16. Research branch: `research/jsp-000404-sharp-centre`.

**Problem status: OPEN.** This checkpoint is not a complete mathematical
proof or disproof. The source-closure gate is also still OPEN.
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` retains its
single executable `sorry`, whose genuine unresolved input is a GLOBAL
non-reusing payment of original terminal debts and translated-loss
duplicates by Boolean true holes OUTSIDE the translated-loss union
and genuinely unreserved surplus.

## Certified Lean repairs

### 1. Common-dominator minimum phase covers

Source: `JSP000404Research/MinimumDominatingPhaseCover.lean`.

The proof now handles the witness from `Nat.find`, strict decreases of
a finite cover after erasure, and reversal of a distinctness hypothesis
without relying on an invalid `.symm` projection.

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38855787098
**SUCCESS** (3,096 jobs). Axiom audits on all four declarations have
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`.

Especially, `slot_injective_on_minimum_cover_of_common_dominator`
proves that a minimum-cardinality cover cannot contain two distinct
obstructions sharing a slot when each slot has a common dominator.
`no_phase_cover_of_common_dominator_turn_slots` then gives the
conditional global phase-cover contradiction.

### 2. Vertex-labelled binary Kraft certificate

Source: `JSP000404Research/LabeledBinaryKraftTree.lean`.

The module now proves the tree/profile depth and label identities,
handles the actual decidable finite-vertex type, fixes list/profile
reindexing, and explicitly specializes the bound on exponents before
using natural-subtraction arithmetic.

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38856107776
**SUCCESS** (3,093 jobs). The audited
`LabeledBinaryKraftTree.Certificate.capacity` and
`LabeledBinaryKraftTree.Certificate.exponent_capacity` declarations
have no `sorryAx`.

The verified **conditional** theorem is:

```text
complete vertex-labelled full binary tree,
one distinct leaf for every vertex v,
leaf depth(v) <= ell(v) = n - exponent(v),
exponent(v) <= n
  => sum_v 2^exponent(v) <= 2^n.
```

An actual geometry-to-labelled-tree certificate satisfying this
depth budget has NOT been constructed from the original planar
hypotheses; its absence prevents promotion to an unconditional
JSP-000404 theorem.

### 3. Saturated seam unit-subslot arithmetic

Source: `JSP000404Research/SaturatedSeamPhaseArithmetic.lean`.

The repaired proof uses a noncomputable real-valued floor-based index,
casts natural truncated subtraction into the reals only after proving
subtraction bounds, and preserves the shared symbol `s` when
applying linear arithmetic to the exact floor identity.

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38856207495
**SUCCESS** (3,216 jobs).
`saturated_wrap_failure_unit_subslot` uses only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

In the theorem's exact saturation and unsafe-seam hypotheses, put
`j = n - floor(z)`, `q = floor(s)`, `s = a + t - z`,
`t = n + delta`, `0 <= delta < 1`. It proves
`q >= 2`, `j < q` and the sharp window:

```text
j + s - q < t - z <= j + delta.
```

## Verification boundary and next mathematical step

These were **three separately kernel-checked modules**, not a complete
workspace build. The historical full Fast Incremental Lean workflow at
head `d019510c487014901924c65c42b61a9c5cf0d4a9`, run
https://github.com/Charlie-Wang-03/awards/actions/runs/38850840471,
FAILED with 384 Lean errors in 49 legacy modules. Focused successes
must not be represented as resolving those other errors; a new full
run requires separate verification.

The currently decisive unproved step remains the globally non-reusing
payment/matching between the actual terminal twin, mixed-rigid and
soft/collision loss debt events and the genuinely eligible
outside-translated true holes plus **unreserved** surplus. Exact
edge/word-multiplicity ledgers and local geometry restrictions alone
do not yield this matching. Neither the conditional Kraft certificate
nor the conditional phase-cover compression supplies that missing
geometric construction.

All new repaired theorems above are `sorry`-free and introduce no
new custom axioms. No complete-problem, eligibility, priority,
submission or award claim is made.


## Follow-on certified repairs (same research branch, October 16)

### 4. Finite terminal dominator compression

Module: `JSP000404Research/FiniteTerminalDominator.lean`.
Focused CI [38858324183](https://github.com/Charlie-Wang-03/awards/actions/runs/38858324183):
**SUCCESS**, 3,097 build jobs, all three `#print axioms` results
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

The injection of minimum covers into their **finite terminal image** and the
conditional phase-cover contradiction are now checked, rather than blocked
by erase-cardinality arithmetic and reverse inequality notation.

### 5. Minimal overweight normalized Kraft profile

Module: `JSP000404Research/MinimalOverweightKraftProfile.lean`.
Focused CI [38858425164](https://github.com/Charlie-Wang-03/awards/actions/runs/38858425164):
**SUCCESS**, combined 3,130 build jobs, all four audited main
profile declarations without `sorryAx`.

Under the stated minimum deletion / post-weight bound hypotheses, with
`a = exponent r`, the normalized total is **exactly**
`sum_v 2^(exponent(v)-a) = 2^(n-a)+1`.
This is an exact conditional overweight profile, not a classification
of all geometric planar exponents.

### 6. Standard residual through-colour promotion

Module: `JSP000404Research/StandardResidualThroughPromotion.lean`.
The SAME [38858425164](https://github.com/Charlie-Wang-03/awards/actions/runs/38858425164)
checks all five audited main declarations, without `sorryAx`.

A through-colour in the standard residual colouring, given genuine
incoming/outgoing same-band outer witnesses and a residual middle edge,
forces both cross-edge directions to lie at least one whole normalized
unit above the through-colour; the top retained through-colour yields
residual cross edges. The correction separates the four independent
band witness inequalities instead of incorrectly chaining tactical
`<;>` and `simpa`.

### 7. Residual binary child recursion

Module: `JSP000404Research/ResidualBinaryRecursion.lean`.
Focused CI [38858699208](https://github.com/Charlie-Wang-03/awards/actions/runs/38858699208):
**SUCCESS**, 3,094 build jobs, all six `#print axioms`
declarations without `sorryAx`.

The code now correctly uses classical decidability for high-source and
high-sink membership in its four weight/exponent definitions and closes
the natural power multiplication orientation. Conditional child mass
bounds `<= 2^(n-1)` still must be supplied by geometry before the
root `<= 2^n` conclusion can be invoked.

### Verification scope

The cited runs are module-specific kernel checks. Do not interpret them
as a green all-module fast build or as a proof that the final WIP
global-payment `sorry` is solved. The main theorem retains that hole,
and the source-closure gate remains open.

### 8. Saturated projected endpoint: full stepwise rigidity

Module: `JSP000404Research/ProjectionSaturatedStepRigidity.lean`.
Focused CI [38859295158](https://github.com/Charlie-Wang-03/awards/actions/runs/38859295158):
**SUCCESS**, 3,310 build jobs; theorem
`ProjectionOrdered.genericProjection_saturated_stepwise_rigidity`
has axioms `[propext, Classical.choice, Quot.sound]`, with
no `sorryAx`.

Given exact projected endpoint saturation and activity of the top
residual colour, the local sorted direction cycle is stepwise tight,
its last direction has floor n, and its wrap gap satisfies the
exact excess/floor identity. This is endpoint-local rigidity,
NOT global non-reuse among debt words or source/blocker carriers.

### 9. Fifth n−3 layer centre: three-transition rigidity

Module: `JSP000404Research/ThirdLayerSaturatedResidual.lean`.
Focused CI [38859461067](https://github.com/Charlie-Wang-03/awards/actions/runs/38859461067):
**SUCCESS**, 3,459 build jobs;
`fifth_deficit_three_forced_support_three_three_transitions`
has axioms `[propext, Classical.choice, Quot.sound]`, without
`sorryAx`.

For a fixed arrangement containing one top (n−1) centre, one
third-layer n−3 support-one centre, and two third-layer n−3
support-two centres, a fifth distinct n−3 centre cannot be
strictly exposed. It must have positive quotient support exactly
three and three sign transitions. This does NOT exclude every
fifth nonexposed centre, nor does it prove the terminal six-source
payment.

### 10. Conditional planar residual recolouring closure

Module: `JSP000404Research/PlanarLowerBranchResidualClosure.lean`.
Focused CI [38860040371](https://github.com/Charlie-Wang-03/awards/actions/runs/38860040371):
**SUCCESS**, 3,266 build jobs, and the theorem
`ProjectionOrdered.planar_lowerBranch_capacity_of_absorbed_residual`
has axioms `[propext, Classical.choice, Quot.sound]`, without
`sorryAx`.

This establishes the actual planar dyadic capacity **conditional**
on the stated one-layer bad-residual implication, a valid residual
recolouring and its safe absorption. The hypotheses do NOT
follow here from arbitrary planar `AngleCap`, and residual
absorption cannot simply be postulated as an unconditional fact.

### 11. Unverified extension frontier

`ThirdLayerTransitionPacking.lean` implements four-centre
transition quotient packing. Its dependent `Fin 4` certificate
and sum normalization were repaired in several iterations,
but until the latest focused run is independently successful it
is NOT listed as certified.

The new `ThirdLayerFifthResidualReduction.lean` aims to
weaken two support-two equalities to support ≤ 2 in the
certified fifth-centre theorem. Its verification depends on
`ThirdLayerTransitionPacking`; no completion claim is
permitted until both build and axiom audit succeed.

## Frozen open mathematical input

In `PlanarLowerBranchProofAdmittedWIP.lean`, the one executable
`sorry` remains at the global six-source terminal debt
inequality. All local or conditional statements above are
strictly weaker and do not constitute the needed outside-U
true-hole + unreserved dyadic-surplus global matching.

## Certified resolution of the third-layer extension frontier

The provisional item "### 11. Unverified extension frontier" above has
now been resolved for the two named modules. The original root global
payment gap remains open.

### 12. Four-centre transition packing

Module: `JSP000404Research/ThirdLayerTransitionPacking.lean`.
Focused CI [38860514844](https://github.com/Charlie-Wang-03/awards/actions/runs/38860514844):
**SUCCESS**, 3,448 build jobs.

Both `third_layer_packing_forces_two_unit_transitions` and
`no_top_three_deficit_three_support_le_two_with_two_support_one`
audit to `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
The main proof constructs genuinely dependent `Fin 4` centre/cycle/
transition-certificate families and normalizes the four actual
quotient terms individually, rather than treating dependent records
as a homogeneous `Matrix.vecCons` vector.

The certified packing forces each of two small-support companion
transition quotients to be exactly one. Consequently, two distinct
n−3 support-one companions cannot coexist with the specified
top-centre/support-one configuration under the strict
`delta < 1/2` geometry.

### 13. Strictly stronger fifth-centre reduction

**New source:** `JSP000404Research/ThirdLayerFifthResidualReduction.lean`.
Focused CI [38860577454](https://github.com/Charlie-Wang-03/awards/actions/runs/38860577454):
**SUCCESS**, 3,461 build jobs.

The new theorem
`fifth_deficit_three_forced_residual_of_two_small_supports`
audits to `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`. Under exactly the five distinct-centre, angle-cap,
n−1/n−3 exponent and one support-one centre hypotheses recorded
in its source, it replaces the two other n−3 companions'
old support=2 assumptions by **support ≤2**, yet concludes that
the fifth n−3 centre has support=3 and exactly three sign
transitions. The internal support=1 possibilities are excluded by
the newly certified four-centre packing theorem, while
support=3 violates the weakened hypotheses.

This is a verified *restricted strengthening*, NOT an arbitrary-
cardinality classification and NOT a proof of the residual
six-source global non-reusing external-hole payment. No new
axioms or executable `sorry` have been introduced.

## Status classification

- The cited focused CI runs each compile their named modules
  and imported dependencies successfully.
- The **full all-module Fast Incremental Lean** has not been
  certified green. Historical modules may still fail independently.
- `PlanarLowerBranchProofAdmittedWIP.lean` retains exactly one
  executable `sorry` at the external-hole/unreserved-surplus
  terminal payment obligation.
- SOURCE_CLOSURE_GATE remains OPEN.
- No full JSP-000404 solution, disproof, or award claim is asserted.


## New sharp five-centre transition/exposure frontier (October 16, follow-on)

### 13. Five-centre transition capacity with arbitrary companion exponents

Source: `JSP000404Research/FiveCentreTransitionCapacity.lean`.
Focused CI [38877905379](https://github.com/Charlie-Wang-03/awards/actions/runs/38877905379):
**SUCCESS** (3,449 build jobs). All three audited declarations use only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

Under planar `AngleCap`, `n >= 4`, `0 <= delta < 1/2`, one top
`n-1` centre `s`, and one distinct `n-3` / support-one centre
`a`, three further **distinct** support-at-most-two centres cannot
exist. The quotient packing obstruction is exact:

```text
q(s) = n; q(a) = n-2;
q(b), q(c), q(d) >= 1;
sum q >= 2*n+1 > 2*n, contradicts planar transition packing.
```

Most importantly, `b,c,d` need not have exponent `n-3` and their
supports need not equal two. If two distinct support<=2 companions
`b,c` exist, **every** further centre `d` obeys
`positiveSupport(d) >= 3` and `centreExponent(d) <= n-3`.
The final exponent inequality uses exact quotient conservation,
not an assumption of a particular fifth-centre layer.

### 14. No extra strictly exposed point, without third-layer conditions

Source: `JSP000404Research/FiveCentreStrictExposure.lean`.
Focused CI [38877905336](https://github.com/Charlie-Wang-03/awards/actions/runs/38877905336):
**SUCCESS** (3,460 build jobs). Axiom audit
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

The same `s,a,b,c` configuration, with **no exponent assumption**
on `b,c` besides support<=2, has no fifth distinct strictly
exposed centre. The five lower turn contributions would be
`n + (n-2) + 1 + 1 + 1 = 2n+1` units, while the strict-support
arc packing bound is `2*pi = 2*(n+delta)*lambda` with
`2*delta < 1`.

### 15. General fifth-centre residual profile

Source: `JSP000404Research/FiveCentreResidualClassification.lean`.
Focused CI [38877944269](https://github.com/Charlie-Wang-03/awards/actions/runs/38877944269):
**SUCCESS** (3,462 build jobs), one audited theorem,
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

Theorem `fifth_general_residual_profile_of_top_third_saturation`:
for any fifth distinct centre `d`, even when the two companions
`b,c` have arbitrary exponents,

```text
positiveSupport(d) >= 3;
centreExponent(d) <= n-3;
NOT StrictlyExposedAt(d);
if centreExponent(d) = n-3 then:
  positiveSupport(d) = 3;
  the canonical lifted sign path has exactly 3 transitions.
```

This is strictly stronger in hypotheses than the previous
`fifth_deficit_three_forced_residual_of_two_small_supports`
theorem: it **removes both** `n-3` exponent assumptions on
the companion centres, and classifies arbitrary fifth centres
outside that layer as well.

### Scope, limits, verification

The preceding three modules are separately Lean kernel-checked.
The sole allowed executable `sorry` in
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
is **not closed**. Its open task remains genuine globally
non-reusing payment for terminal twin, mixed-rigid,
soft/covered translated blockers and NET duplicate debt by
Boolean holes **outside** translated loss, plus legitimately
unreserved dyadic surplus. These new geometric third-layer
restrictions do not automatically provide that payment or
a geometry-to-dyadic allocation.

The historical all-module Fast Incremental Lean workflow is
**not certified green**. Focused green runs alone do not
establish global build success or an unconditional solution.


## October 16: global-exposure classification and direct Hall repairs

### 16. Odd minimum exponent layer in minimal overweight deletion

Module: `JSP000404Research/MinimalOverweightParity.lean`.
CI [38879651663](https://github.com/Charlie-Wang-03/awards/actions/runs/38879651663):
**SUCCESS**, 3,096 build jobs; four audited key declarations show
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

Fixed the obsolete `odd_pow_iff` reference with an actual
modulo-two proof using positive exponent/evenness, and repaired the
three-element Finset cardinal bound with two explicit
`Finset.card_insert_le` inequalities.

Conditional on exact normalized overweight mass and the
minimum-deletion child bound, the multiplicity of the minimum exponent
is **odd**, and cannot be exactly two. These child-bound hypotheses
are not established automatically for arbitrary planar geometry.

### 17. Global exactly-four strict exposure classification

Module: `JSP000404Research/FourExposedCentreSaturation.lean`.
CI [38880432513](https://github.com/Charlie-Wang-03/awards/actions/runs/38880432513):
**SUCCESS**, 3,461 build jobs. The one audited iff theorem has only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
The first CI attempt failed only because the runner could not resolve
`release.lean-lang.org`; after retry, a separate Lean error
(`hds.symm` on function-shaped inequality) was corrected with
`Ne.symm`, and final focused build passed.

Under the four-centre saturation configuration from the previous
checkpoint (top n−1 centre s, n−3/support-one centre a, and two other
support<=2 centres b,c), for EVERY vertex d:

```text
StrictlyExposedAt p d <-> (d=s or d=a or d=b or d=c).
```

This is global over the entire finite point set under the **specific**
saturated configuration. It does NOT assert that every general planar
configuration has four exposed points, nor does it establish the
missing global dyadic payment.

### 18. Repaired planar Hall hard-word outlet

Module: `JSP000404Research/PlanarLowerBranchHallOutlet.lean`.
CI [38880437723](https://github.com/Charlie-Wang-03/awards/actions/runs/38880437723):
**SUCCESS**, 3,533 build jobs. All three audited declarations have
only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

Fixed a misapplied Subtype extensionality, added the projected
linear order in the cycles binder and final theorem goal, and
restored the actual scale lemma import. The verified conditional
Hall route is:

```text
forall hard word x, candidates(x) subset ACTUAL projectionHoleWords;
forall finite hard-word subsets S,
  |S| <= |union_{x in S} candidates(x)|
==> exists a global injection hardProjectionWords -> projectionHoleWords
==> sum_v 2^exponent(v) <= 2^n.
```

The **global Hall expansion** and genuine hole candidate construction
have NOT been proved from AngleCap. Treating these assumptions as
unconditional would be circular. This is a restored proof
interface, not a discharged final `sorry`.

### Still outstanding

The last admitted research-only WIP `sorry` remains in
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
(near line 632). The decisive missing geometric step remains
globally non-reusing payment of translated-loss-covered blockers,
terminal twin/mixed-rigid/soft debts, and genuine NET duplicate
debt by TRUE Boolean holes *outside* translated losses plus
genuinely unreserved dyadic surplus.

Do not conflate these focused build successes with the full
Fast Incremental Lean workflow: that historical all-module
build remains red because of unrelated legacy Lean errors.


### 19. Enlarged-loss unique Hall collision neighbour

Module: `JSP000404Research/ResidualEnlargedLossCollisionGraph.lean`.
Focused CI [38881237514](https://github.com/Charlie-Wang-03/awards/actions/runs/38881237514):
**SUCCESS**, 3,323 build jobs. The audited main declaration
`OrderedEdgeColoring.minimal_enlargedCandidate_loss_unique_neighbor_is_loss`
depends only on `[propext, Classical.choice, Quot.sound]`,
without `sorryAx`.

Lean repairs: reconstruct the shared-block source via the explicit
`Finset.mem_inter` and `Finset.mem_biUnion` witnesses, replace the
unimported `BlocksCross` predicate with a concrete nonempty finite-block
intersection, and resolve the external-vertex inequality with a typed
`v != w` proof rather than a failing dependent `subst`/rewrite.

**Actual consequence:** For a minimal deficient enlarged-projected
candidate family, if a loss vertex v has a **unique collision neighbour**
w and `exponent(v) < n`, then w must itself be a projected-loss
vertex. If w were non-loss, its candidate block would be Q_w and its
intersection with the entire enlarged-loss block of v would have at
most |Q_v| words, contradicting the certified minimum-deficiency
shared-block lower bound |Q_v|+1.

This reduces a possible Hall obstruction to at least two interacting
loss vertices, but does NOT rule out multiple loss neighbours or
pay the global terminal/NET/translated debts. It is a conditional
structural exclusion, not a proof of all Hall expansion instances.


## October 16 continuation: actual canonical candidate and rank repairs

### 20. Planar local Boolean candidate capacity

Source `JSP000404Research/ProjectionLocalCandidateCapacity.lean`.
Focused CI [38883162408](https://github.com/Charlie-Wang-03/awards/actions/runs/38883162408):
**SUCCESS**, 3,522 jobs, no `sorryAx` in audited theorem.

The concrete lower-branch geometric hypotheses imply for **each**
projected centre a finite Boolean candidate block `B_v` with
`2^exponent(v) <= |B_v|`: retained completion cube for
non-loss centres, retained-active single-coordinate doubled completion
block for loss centres. Repair was explicit projected linear order
in the cycle binder and the actual Sendov scale-lemma import.
This closes LOCAL block sufficiency only; global Hall expansion remains
open.

### 21. Saturated hard overlap to TWO planar rigid endpoint certificates

Source `JSP000404Research/ProjectionSaturatedOverlapRigidity.lean`.
Focused CI [38883928522](https://github.com/Charlie-Wang-03/awards/actions/runs/38883928522):
**SUCCESS**, 3,533 jobs, audited axioms
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

`saturatedSaturatedWord_has_two_wrap_rigid_endpoints` reconstructs
the ordered actual residual carrier `u < v` from a simultaneously
saturated hard overlap Boolean word. Both endpoints admit concrete
local cut-rotated cycles with top floor band n and exact wrap-gap
equality. Restored projected typeclass scope and natural-to-real
`n+1` coercions. This is geometric evidence but not a nonreuse
allocation for the remaining Boolean hole debt.

### 22. Overweight implies a genuinely MINIMAL NONSINGLETON Hall core

Source `JSP000404Research/ProjectionWeightedBlockHallReduction.lean`.
Focused CI [38885289459](https://github.com/Charlie-Wang-03/awards/actions/runs/38885289459):
**SUCCESS**, 3,533 jobs; new theorem
`planar_lowerBranch_overweight_has_nontrivial_candidate_core`
audited `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
Three prior declarations in same module also audited sorry-free.

For the actual chosen single-flip candidate family, if the dyadic
mass really exceeds `2^n`, there must exist an inclusion-minimal
deficient set T with **|T| >= 2**:

```text
card (union_{i in T} B_i) < sum_{i in T} 2^k(i);
forall U strict-subset T: NOT BlockDeficient(U).
```

This is an unconditional NECESSARY obstruction under AngleCap and
lower-branch hypotheses, obtained by contrapositive of the certified
weighted block capacity outlet and by excluding singleton deficit
using the newly certified local candidate bounds. It is NOT a proof
that this core cannot exist; a global collision/Hall expansion
exclusion is still missing.

Repair details: eliminated invalid parameter-dependent projected-order
`local instance`, explicitly bound the order for each `C` family,
proposition and proof, repaired import ordering, and proved the
singleton `biUnion` equality by `Finset.ext`.

### 23. Well-founded weighted hard recursion rank

Source `JSP000404Research/ResidualWeightedRecursionRank.lean`.
Focused CI [38885649486](https://github.com/Charlie-Wang-03/awards/actions/runs/38885649486):
**SUCCESS**, 3,092 jobs. Five audits only
`[propext, Quot.sound]`, no `sorryAx`.

Exact rank `payload*(n+1) + (n-freeDim)` decreases when payload
strictly drops or payload holds constant while free dimension
strictly grows, under the stated dimension bounds. Separate
`payload*(n+1) + exponent` rank similarly decreases under
strict payload or exponent descent. Repairs made multiplication
distributivity explicit rather than incorrectly asking `omega`
to reason over opaque nonlinear atoms, and opened a conjunctive
equality before substitution.

These are VALID well-founded ranking functions conditional on
actually constructed progress steps; geometric existence of
a valid globally nonreusing payment step is NOT yet established.

### 24. Source encoding and remaining legacy build work

`JSP000404Research/ProjectionEnlargedCandidateHallGraphFree.lean`
contained **129 literal escaped newline strings** and zero real
newlines. Repaired 130 actual source lines, commit
`e4c58334801aa3949f96e12563f1efd33bcb6143`.
Focused job [38884935035](https://github.com/Charlie-Wang-03/awards/actions/runs/38884935035)
was RED from existing *upstream dependency* errors,
including the invalid legacy Mathlib import of
`SecondLayerFourSupportReduction`. The latter import was replaced
by `Mathlib.Data.Fin.VecNotation`, commit
`3bc0dbda25cfb8010d1a6a2c4b9bd31f7024a99c`.
Neither target is declared fully Lean-verified until its focused
build succeeds.

### Mathematical scope

Main WIP `PlanarLowerBranchProofAdmittedWIP.lean` retains its sole
executable `sorry` (line 632 in checked HEAD). Local candidate
sufficiency, forced minimal non-singleton Hall cores, conditional
connectedness, and termination rankings DO NOT prove the actual
global Boolean hole and unreserved dyadic-surplus payments. Historical
Fast Incremental Lean still has unrelated legacy compilation errors.


### 25. Connected non-singleton ACTUAL planar Hall obstruction (verified)

Source: `JSP000404Research/ProjectionConnectedHallCore.lean`.
Focused CI [38885806510](https://github.com/Charlie-Wang-03/awards/actions/runs/38885806510):
**SUCCESS**, 3,534 build jobs; one audited theorem using only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

If the actual planar lower-branch dyadic mass is overweight, then the
canonical single-flip block family possesses an inclusion-minimal
deficient core `T` with `2 <= |T|` such that for EVERY partition
`T=A union B` into nonempty disjoint parts the candidate unions
INTERSECT:

```text
NOT Disjoint (union_{v in A} candidateBlock(v))
             (union_{w in B} candidateBlock(w)).
```

Thus the candidate-block intersection graph on T is connected.
This is a strictly stronger NORMAL FORM for a hypothetical
counterexample than the standalone minimal non-singleton Hall core.
It reduces the possible global obstruction to connected collisions,
but does not prove that those collisions cannot exist.

### Legacy focused-build blocker accounting

The restored newline source
`ProjectionEnlargedCandidateHallGraphFree.lean` is syntactically
readable but [CI 38884935035](https://github.com/Charlie-Wang-03/awards/actions/runs/38884935035)
FAILED because its deep imports were red
(`SecondLayerFourSupportReduction`,
`FourCentreTransitionCases`, legacy recursion dependencies, etc.).
Fixing the invalid old Matrix.Notation import exposed additional
`FourCentreTransitionCases.lean` errors;
[CI 38885709550](https://github.com/Charlie-Wang-03/awards/actions/runs/38885709550)
remains FAILED. These files are **NOT** certified Lean-green.

Four meaningful focused successes this continuation plus the
connected core success are separately proved, and in no sense
establish that the all-module Fast Incremental Lean run is green.
The source-closure gate remains OPEN with the sole root executable
`sorry` in `PlanarLowerBranchProofAdmittedWIP.lean`.


### 26. Genuine two-centre enlarged Hall obstruction excluded if either centre is loss (NEW, verified)

Source: `JSP000404Research/ResidualEnlargedPairLossHall.lean`.
Focused GitHub Actions [38888157635](https://github.com/Charlie-Wang-03/awards/actions/runs/38888157635):
**SUCCESS**, 3,313 jobs. The theorem
`OrderedEdgeColoring.enlargedCandidate_pair_capacity_of_one_loss`
has audited axioms `[propext, Classical.choice, Quot.sound]` and
NO `sorryAx`.

For two distinct vertices `v != w`, with one-layer residual
constraints (`exponent(x)<n`, `exponent(x)<=n`,
`card(active(x)) <= n-exponent(x)+1`), provided
at least one endpoint belongs to `projectedLossVertices`, we have:

```text
card(enlargedProjectedCandidateBlock(v) UNION
     enlargedProjectedCandidateBlock(w))
    >= 2^exponent(v) + 2^exponent(w).
```

The proof uses genuine quantified one-cube extra slack at each
loss vertex and audited intersection caps:
- LOSS/NO-LOSS: intersection <= |Q_loss|;
- LOSS/LOSS: intersection <= |Q_v| + |Q_w|.
The exact finite-union card identity then gives the combined
weighted Hall bound. This excludes EVERY two-centre enlarged-candidate
Hall defect containing a projected-loss centre; any such
loss-containing minimal deficient core needs >=3 centres.

This conclusion is for the **all-active enlarged family**,
not an automatic two-centre theorem for the unrelated
single-choice `planarLowerCandidateBlock` family.

Original JSP-000404 root remains incomplete: no unrestricted
global non-reusing payment from TRUE external Boolean holes and
unreserved surplus has been obtained.


### 27. Maximal loss leaf rigidity restored without sorry (NEW, verified)

Source: `JSP000404Research/ResidualEnlargedLossLeafRigidity.lean`.
Focused CI [38888804586](https://github.com/Charlie-Wang-03/awards/actions/runs/38888804586):
**SUCCESS**, 3,327 jobs. Both audited declarations use only
`[propext, Classical.choice, Quot.sound]` and NO `sorryAx`.

For an inclusion-minimal deficient enlarged candidate family and a
LOSS centre whose completion cube is maximal among loss centres, if
the vertex has a unique collision neighbour inside the deficient
core, then its retained-active palette has EXACTLY TWO colours,
and `exponent(v)=n-1`. Lower-exponent maximal loss leaves are excluded.
Fixes comprised explicit intersection/biUnion membership certificates,
correct reversed inequality orientation for distinct endpoints,
deriving the loss target from the actual `projectedFree` identity,
and ring/omega-safe factor decomposition with natural subtraction.

Together with the new genuine pairwise loss expansion (Section 26),
the two-centre loss case is eliminated entirely and a loss leaf
in a larger deficient core is restricted to the top exponent.
No unconditional global hole/surplus nonreuse exists.


### 28. Certified two-vertex deficient core is NONLOSS-ONLY

Source: `JSP000404Research/ResidualEnlargedTwoVertexDeficiency.lean`.
Focused CI [38888919527](https://github.com/Charlie-Wang-03/awards/actions/runs/38888919527):
**SUCCESS**, 3,315 jobs; audited
`two_vertex_enlarged_deficiency_forces_both_nonloss` uses only
`[propext, Classical.choice, Quot.sound]`, NO `sorryAx`.

For any `v != w`, under actual one-layer profile hypotheses,
an actual `BlockDeficient` witness for `{v,w}` of the enlarged
all-active residual candidate family entails
`v notin projectedLossVertices` AND
`w notin projectedLossVertices`.
The kernel proof opens the literal `BlockDeficient` predicate,
proves exact two-element `biUnion` and demand-sum identities,
and contradicts Section 26's audited weighted pair bound.

As a result, the two-centre loss branch is NOT merely verbally
dismissed; it has a reusable Lean theorem in the exact global
obstruction vocabulary. A loss-containing enlarged minimal deficient
core must involve THREE OR MORE distinct centres.
This does NOT apply without proof to other (single-choice) candidate
families, and does NOT rule out all larger cores.

The original `PlanarLowerBranchProofAdmittedWIP` STILL has exactly
one admitted global hole/unreserved-surplus nonreuse payment,
so the full JSP-000404 proof remains open. 
