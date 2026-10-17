# JSP-000404 — top-inclusive three-layer capacity and two Lean module repairs

Date: 2026-10-17. Downstream repository: `Charlie-Wang-03/awards`.
Working branch: `research/jsp-000404-sharp-centre`.

## A. Incoming verified state

Prior lower-branch main WIP integration of a geometric third-layer
support-one multiplicity bound (only one such OTHER centre above an
actual top when n>=5) was verified in three independent focused runs:
- https://github.com/Charlie-Wang-03/awards/actions/runs/39035967586 — SUCCESS
- https://github.com/Charlie-Wang-03/awards/actions/runs/39035967595 — SUCCESS
- https://github.com/Charlie-Wang-03/awards/actions/runs/39035967587 — SUCCESS

Latest COMPLETED full Fast Incremental Lean run before this round:
https://github.com/Charlie-Wang-03/awards/actions/runs/39035967654
FAILURE, 248 historical diagnostics across optional modules.
These are compiler diagnostics, not 248 mathematical admissions.

## B. NEW TRUE-MATH top-inclusive three-layer capacity closure

File: `JSP000404Research/TopLayerThreeLevelDyadicCapacity.lean`.

For finite natural exponent data `k : V -> Nat`, `n>=4`,
and `forall i, k(i)<=n-1`, set

- m = card(V);
- r = card {i | k(i) = n-1};
- q = card {i | k(i) = n-2};
- u = card {i | k(i) = n-3}.

All other exponents are <=n-4, giving the **exact natural bound**

  sum_i 2^k(i) <= (m + 7*r + 3*q + u) * 2^(n-4).

Thus the conditional profile criterion `m+7r+3q+u<=16`
PROVES `sum_i 2^k(i)<=2^n`.

The geometric specialization uses actual injective planar `AngleCap`
and genuine `CentreProjectiveCycle` exponents, where the existing
proved `centreExponent_lt_n` guarantees `k(i)<=n-1`.
It does NOT assume that the top layer is absent, unlike the prior
two-layer criterion.

Additional theorem:
`planar_overweight_forces_top_three_layer_count_excess`.
Any ACTUAL overweight configuration with n>=4 must satisfy
`m+7*r+3*q+u>16`. This is a necessary census
obstruction, not a counterexample.

Examples closed by this certificate:
- m=6, r=1, q=0, u<=3;
- m=7, r=1, q=0, u<=2;
- m=5, r=1, q=1, u<=1.

**Focused kernel CI**:
https://github.com/Charlie-Wang-03/awards/actions/runs/39038671672
SUCCESS, 3227 Lake jobs. All THREE theorem `#print axioms`
reports exactly `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`. No synthetic TRUE-hole / surplus reuse is invoked.

**Root integration**:
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
now branches on the exact top-inclusive weighted census BEFORE the
previous no-top and uniform-drop cuts, so the sole unresolved geometric
payment applies only when this additional sufficient condition FAILS.
Commit: `05600758bc3102e9750f0cc5a9775514b7bfbb95`.
The EXACTLY ONE executable original `sorry` is now line 779.
Its six-source global geometry is still NOT proved.

Focused integration workflows for this commit:
- https://github.com/Charlie-Wang-03/awards/actions/runs/39038839142
- https://github.com/Charlie-Wang-03/awards/actions/runs/39038839212
- https://github.com/Charlie-Wang-03/awards/actions/runs/39038839114
At the time of writing these were in progress. Do not count them
as passed without checking their final conclusions.

## C. Historical Lean repair — SixPointNoTwoSupportOneMinima

Module `JSP000404Research/SixPointNoTwoSupportOneMinima.lean`
previously generated FOUR Lean diagnostics. Fixed the shadowed
`lam` parameter and replaced a redundant stale analytic
calculation with the already independently certified actual
sharp-centre contradiction
`no_two_third_support_one_around_sharp_n_ge_five`.
Actual sharpness is obtained from the real top exponent via
`concrete_unit_deficit_is_sharp`; NO old theorem conclusion
was weakened.

Focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39038437300
SUCCESS, 3496 Lake jobs. Printed theorem axioms exactly
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

## D. Historical Lean repair — OverweightStableMax

Module `JSP000404Research/OverweightStableMax.lean`
previously generated TWELVE diagnostics. Restored finite erase
type-class elaboration with an explicit, classically constructible
`[DecidableEq V]` instance argument (not a mathematical
geometry assumption). Removed a redundant tactic after the
finite-sum rewrite; provided the concrete summand function to
`Finset.single_le_sum`; replaced an unavailable
`Nat.pow_lt_pow_iff_right₀` constant with a direct monotone-powers
contradiction.

The existing mathematical statements are preserved:
a no-compensated deletion column has total bonus less than the
deleted centre's weight; a max-exponent centre is bonus-stable;
an unstable maximal centre forces a compensated deletion.

Focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39038542869
SUCCESS, 3094 Lake jobs. All THREE printed theorem axioms exactly
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

These two repairs independently clear 16 previously observed
diagnostics. This does NOT assert the entire large optional tree
now passes or that fresh full-diagnostic total equals 248-16.

## E. Genuinely open core

There remains one executable main WIP `sorry`, not moved to
a different unchecked axiom. The open statement is genuine
global non-reusing six-source payment of ACTUAL retained-edge
hard/soft/mixed/twin carriers, covered blockers, NET duplicate
debt, and projected profile loss into distinct literal external
Boolean TRUE holes and genuinely unreserved dyadic surplus.
Local cardinality sufficient conditions or geometric exclusions
cannot be substituted for that global payment.
JSP-000404 is NOT yet proved or disproved.

## F. New geometric corollary: eight-centre top/no-next support-one

Module `JSP000404Research/SevenCentreTopThirdSupportOneCapacity.lean`
retains a seven-centre named corollary but now establishes the stronger
`planar_eight_centre_top_no_next_third_support_one_capacity`.

It combines the ACTUAL planar top uniqueness theorem,
`top_third_support_one_count_le_one_n_ge_five`, and the top-inclusive
three-level dyadic budget. In an injective real `AngleCap`
configuration with `n>=5`, `3<=card V<=8`, an actual exponent
`n-1` top centre, NO exponent `n-2` centre, and every exponent
`n-3` centre having quotient support exactly ONE, geometry forces
the count values `r=1,q=0,u<=1`. Consequently
`m+7*r+3*q+u<=8+7+1=16`, which PROVES the original dyadic capacity
without six-source TRUE-hole payment.

This is a real geometric sufficient subcase; it does NOT claim all
third-layer centres universally have quotient support one. It is a
geometric COROLLARY of the root's top-inclusive numerical census
branch, not an additional logically disjoint root case.

Dedicated check of initial seven-centre draft:
https://github.com/Charlie-Wang-03/awards/actions/runs/39039257910
FAILED for an invalid old Finset lemma name, not for a mathematical
counterexample. The exact zero-count obligation was replaced with
`simp [M, hnoNext]`, while the bound was sharpened to eight centres.
New targeted check:
https://github.com/Charlie-Wang-03/awards/actions/runs/39039536716.
It was still pending at time of this report revision. Until verified,
do NOT mark this eight-centre geometric corollary as kernel certified.

The main original six-source payment remains the ONE original `sorry`.
