# JSP-000404 — exact n=3 large-centre proof frontier (2026-10-26)

**Status: RESEARCH ONLY. The original all-n theorem is neither proved nor disproved.**

Branch: `research/jsp-000404-connector-compiler-repair-20261024`. The sole executable research admission remains `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean:935`; its full global eight-source payment under actual AngleCap is unproved. This document records *necessary* geometry and exact capacity equivalences, not a new licence to claim complete JSP-000404.

## Verified exact dyadic census

At n=3, t=3+delta, 0<=delta<1/2, every original `centreExponent` is 0, 1 or 2. For the genuinely original projective cycle family, writing N=card(V) and N_j the number of original centres of exponent j,

    sum_i 2^k_i = N + N_1 + 3*N_2.

For N>=7, the full n=3 capacity inequality `sum_i 2^k_i <= 8` is **equivalent** to exactly one of:

- N=7, N_2=0, N_1<=1;
- N=8, N_1=0 and N_2=0.

N>=9 cannot satisfy this numerical capacity. Conversely, a hypothetical n=3 overweight configuration with N>=7 must lie in the exact alternative:

1. N>=9, with any admissible exponent counts;
2. N=8 and at least one exponent-1 or exponent-2 centre;
3. N=7 and either at least two exponent-1 centres or at least one exponent-2 centre.

These exhaust the **numerical** alternatives; actual planar impossibility of (1)-(3) is NOT established by this classification. The existing original WIP root already disposes of many numerically safe branches, so this result clarifies the remaining target rather than eliminating the final sorry.

File: `JSP000404Research/PlanarThreeSharpOverweightClassification.lean`.

Kernel evidence: [run #40355024773](https://github.com/Charlie-Wang-03/awards/actions/runs/40355024773), SUCCESS; 3552 Lake jobs. All four named theorems printed `[propext, Classical.choice, Quot.sound]` with no `sorryAx`:

- `three_level_dyadic_sum_exact`
- `planar_three_original_top_next_exact_ledger`
- `planar_three_large_capacity_iff_exact_profile`
- `planar_three_large_overweight_iff_obstruction_profile`

## Verified original-plane narrow-gap constraint on the top-exponent motif

The exponent-two branch `k_i=2`, for any original centre at n=3, forces **positive quotient support exactly ONE and quotient sum exactly THREE**. If actual geometry additionally has N>=7 and satisfies AngleCap, then among its N-1 actual projective gaps, exactly N-2 have zero integer quotient. Each is strictly positive, and all at this same original centre share a *single* scaled remainder budget <=delta.

Consequently there exists a **genuine positive original gap** g with

    quotient(g)=0, g>0, (N-2)*(3+delta)*g <= delta.

This is stronger than the separate `(N-4)` bound for a saturated support-three centre, but neither may be interpreted as a true exterior Boolean hole or globally unreserved dyadic credit. Neither is a cross-centre disjointness statement.

File: `JSP000404Research/PlanarThreeCrowdedTopTinyGap.lean`.

Kernel evidence: [run #40355721853](https://github.com/Charlie-Wang-03/awards/actions/runs/40355721853), SUCCESS; 3551 Lake jobs. Both named theorems printed exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`:

- `planar_three_top_centre_has_exact_unit_support`
- `planar_three_crowded_top_forces_n_minus_two_tiny_gap`

## The remaining genuinely mathematical gates

1. **Original n=3 real-plane geometry:** exclude the three overweight profiles above from actual AngleCap or otherwise prove the bound. Gap narrowness alone does not rule out their realization. In particular, the necessary upper bound `N<=8` is NOT currently proved for the entire positive-delta n=3 strip.
2. **All-n global payment:** under the original (unrestricted) AngleCap hypotheses, find a source-native, non-reusing allocation of **all eight actual source-debt classes** to only (a) truly uncovered exterior Boolean words and (b) genuinely available unreserved dyadic surplus. Overlap/soft-covered words and reserved capacities are not valid substitutes.
3. **Formal proof audit:** do not state the root theorem is complete until the single deliberate `sorry` is eliminated by valid mathematics, the full root builds, and its `#print axioms` no longer contains `sorryAx`.

Previous relevant exact-source obstruction: `ActualEighthNoBicolourHallHardStop.lean`, [run #40348337643](https://github.com/Charlie-Wang-03/awards/actions/runs/40348337643), proves local eighth-lane true-hole Hall payment is impossible in the specified no-two-bicolour-owner regime when genuine candidates exist. The missing credit cannot be assumed to arise from that local route.

**No new admitted declarations or custom axioms. No upstream award/proof submission. Keep PR #6 Draft/Open/Unmerged.**
