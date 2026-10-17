# JSP-000404 — Eight-centre support obstruction, nine-centre fourth-scale frontier and legacy Lean repair

Date: 2026-10-17. Research branch: `research/jsp-000404-sharp-centre`.
This is a factual work checkpoint, NOT a global proof/disproof.

## Confirmed old main-root checks

The previous top-inclusive weighted dyadic census and genuine top/third
support-one invariant compiled in the main `PlanarLowerBranchProofAdmittedWIP.lean`
at the previous research baseline.

## Newly completed: actual eight-centre geometric branch

The independently kernel-certified
`planar_eight_centre_top_no_next_third_support_one_capacity`
in `JSP000404Research/SevenCentreTopThirdSupportOneCapacity.lean`
was dispatched as a new `by_cases hEightTopThirdSupportOne` before
the earlier top-inclusive profile budget. For actual injective planar
`AngleCap` cycles, with `n>=5`, `3<=card V<=8`, a true top
`n-1` centre, no `n-2` centres, and every original `n-3`
centre having actual positive quotient support ONE, the
`sum_i 2^k(i)<=2^n` objective is proven.

Main integration commit: `69b3e880a9313d342f975c76b2efd384f9cb47bf`.
All three actual root integration checks SUCCEEDED:
- https://github.com/Charlie-Wang-03/awards/actions/runs/39040815324
- https://github.com/Charlie-Wang-03/awards/actions/runs/39040815277
- https://github.com/Charlie-Wang-03/awards/actions/runs/39040815273

The root still contains exactly ONE pre-existing executable `sorry`
around line 799 (after this integration). That sorry still encompasses
the unrestricted six-source nonreusable payment into actual
TRUE external holes and genuinely UNRESERVED surplus.

## Newly completed: genuine support-two/three necessary witness

`planar_eight_centre_overweight_requires_third_support_two_or_three`
in `SevenCentreTopThirdSupportOneCapacity.lean` proves:

With the preceding planar eight-centre, `n>=5`, true-top
and no-next-layer prerequisites, an overweight profile
`2^n < sum_i 2^k(i)` MUST contain a genuine `n-3`
centre whose positive quotient support is precisely 2 OR 3.
It follows from (i) the existing actual eight-centre capacity
corollary and (ii) `concrete_deficit_three_structure`,
whose support possibilities are exactly 1/2/3.

Kernel CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39041041761
SUCCESS, 3508 Lake jobs; the new theorem printed
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

This is a conditional necessary obstruction, NOT a constructed
counterexample and NOT a global no-hole payment theorem.

## Newly completed: historical two-bad support case classifier

File: `JSP000404Research/TwoBadSupportCaseSplit.lean`.
The latest previously completed full build showed five diagnostics
around a missing `Fintype V`, an incomplete `i : V` binder,
and an accidentally shadowed lambda. These were corrected.
The module retains exactly the original support possibilities
`(1,2),(2,1),(1,3),(3,1),(2,2),(2,3),(3,2),(3,3)`
for two distinct n-3 centres alongside a top n-1.
The impossible `(1,1)` follows from the independently proven
geometric exclusion; no source contract or theorem goal was
weakened.

Kernel CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39041390790
SUCCESS, 3497 Lake jobs; both printed axioms
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## Submitted and pending verification

### Historical ProjectiveCutRotation repair

File `JSP000404Research/ProjectiveCutRotation.lean`.
The seven old diagnostics involved obsolete simplification behavior
for `getLastD`, the wrong orientation of the list rotation theorem,
a computability mistake for `Real.pi`, and missing list append
normalization. Current repairs use `List.getLastD_cons`,
`List.getLast?_append_cons`, `noncomputable def`,
and explicit block-append rotation.
Dedicated check:
https://github.com/Charlie-Wang-03/awards/actions/runs/39041568250
**SUCCESS**, 3218 Lake jobs; all EIGHT printed theorems with only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
All seven previously counted diagnostics in this module are repaired.

### A four-layer capacity census and true nine-centre subcase

File `JSP000404Research/NineCentreTopFourthLayerCapacity.lean`.
For `n>=5`, writing `m=|V|`, `r_j=#{i | k(i)=n-j}`,
the exact dyadic budget
`sum_i 2^k(i) <= (m+15*r1+7*r2+3*r3+r4)*2^(n-5)`
holds whenever `k(i)<=n-1`.
The criterion `m+15*r1+7*r2+3*r3+r4<=32`
is sufficient for capacity (it is NOT universal).

Combining actual top uniqueness with the already certified
at-most-one third-layer support-one exclusion, the nine-centre
geometric corollary assumes an actual top `n-1`, NO next
`n-2`, all `n-3` centres support-one, and *additionally*
at most FIVE actual `n-4` centres. With `m<=9`,
the count is `m+15+0+3+5<=32`.
The fourth-layer-count restriction is additional geometric profile
information, NOT derived from all `AngleCap` configurations.

First CI identified a normalization oversight for the abbreviation
`k` in a natural-number exponent inequality; this was repaired
without adding a `sorry`.
Second focused check:
https://github.com/Charlie-Wang-03/awards/actions/runs/39041607212
**SUCCESS**, 3509 Lake jobs. Both printed theorems have only
`[propext, Classical.choice, Quot.sound]` and NO `sorryAx`.
The nine-centre capacity theorem was dispatched as an explicit
conditional geometric branch before the eight-centre branch in the
admitted WIP main root in commit
`daa2644221914f36e386180aa605129fb788cc5b`.
Exactly ONE original root `sorry` remains (near line 822).
Main-root targeted integration CI was launched at that SHA; verify
its conclusion independently before marking this insertion as green:
https://github.com/Charlie-Wang-03/awards/actions/runs/39042018472
https://github.com/Charlie-Wang-03/awards/actions/runs/39042018468
https://github.com/Charlie-Wang-03/awards/actions/runs/39042018515

## Full tree and remaining mathematical obligation

The most recently evaluated full Fast Incremental Lean run
https://github.com/Charlie-Wang-03/awards/actions/runs/39039536749
FAILED with 248 historical Lean diagnostics in optional modules,
distinct from the one actual outstanding WIP global mathematical
`sorry`. Later whole-tree jobs should be used to refresh the
diagnostic count when they finish.

The true remaining open obligation is the original-edge six-source
non-reusing allocation of hard/soft/mobile/twin/mixed and NET
duplicate liabilities plus projected profile loss to LITERAL external
TRUE holes and GENUINELY unreserved dyadic surplus. Existing finite
cardinality slices, arithmetic profile lemmas, sharp-centre exclusions
and older conditional ledgers have not closed the general payment.

## Further work submitted: genuine deletion-bonus implementation

`JSP000404Research/UnitGainDeletionBonus.lean` has been repaired
with an explicitly classical noncomputable `unitGainDeletionBonus`
for arbitrary vertex types, an explicit `DecidableEq V` typeclass
for actual Finset erasure operations, proof of the dyadic
two-times-weight equation, and non-brittle fully applied
maximal-centre stable/compensated deletion theorems.
The original bonus-matrix conclusions were kept.

Initial focused check #39041976745 failed, and the subsequent
retry #39042248581 identified a final conditional-split script
issue. Final correction used `if_neg` and kept the exact
nondecrease / compensated deletion mathematical contracts.

Final focused CI
https://github.com/Charlie-Wang-03/awards/actions/runs/39042413343
**SUCCESS**, 3096 Lake jobs. All FOUR printed theorems depend
only on `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`. The 11 historical diagnostics of this module
were removed without weakening its conclusions.

## Independently submitted further actual nine-centre obstruction

`JSP000404Research/NineCentreOverweightSupportOrFourthObstruction.lean`
strengthens the nine-centre conditional capacity certificate
to an explicit necessary dichotomy without an assumed fourth-layer
count: with n>=5, 3<=card V<=9, a true top centre n-1,
and no second layer n-2, ANY actual overweight configuration
must EITHER possess a third-layer n-3 centre of quotient
support TWO or THREE, OR have at least SIX actual n-4 centres.

This is derived from actual centre exponent/support constraints and
the prior kernel-verified nine-centre certificate. It is not
a construction of an overweight set and does not close the
unrestricted six-source payment.

Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39042547507
was still in progress at this checkpoint; do not count this
new dichotomy as verified until `#print axioms` and Lake pass.
