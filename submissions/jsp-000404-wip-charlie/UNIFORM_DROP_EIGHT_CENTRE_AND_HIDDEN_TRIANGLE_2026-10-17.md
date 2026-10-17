# JSP-000404 — Uniform exponent-drop branch and repaired hidden-angle triangle

Date: 2026-10-17
Branch: `research/jsp-000404-sharp-centre`.
Scope: verified conditional capacity theorem, expanded admitted-root dispatch, and historical Lean repair. **Not an original global solution.**

## A. Existing root integration audited at start

The previous five-centre and six-centre geometric dispatch integrated into
`PlanarLowerBranchProofAdmittedWIP.lean` was **SUCCESS** in three
independent focused runs:

- Admitted WIP https://github.com/Charlie-Wang-03/awards/actions/runs/39028964777
- Four-centre/lower branch https://github.com/Charlie-Wang-03/awards/actions/runs/39028964739
- Actual external-hole interface https://github.com/Charlie-Wang-03/awards/actions/runs/39028964748

The latest previously completed full Fast Incremental Lean
https://github.com/Charlie-Wang-03/awards/actions/runs/39029221914
FAILED with 263 historical error diagnostics across old optional modules.
It is not a counterexample to the original problem and not 263 mathematical
`sorry` obligations.

## B. New independent unconditional arithmetic theorem

File: `JSP000404Research/EightCentreNoHighLayerCapacity.lean`.

`dyadic_capacity_of_uniform_exponent_drop`:

For any finite set `V`, natural exponent profile `k`,
and integers `0 <= d <= n`, if
`Fintype.card V <= 2^d` and `forall i, k i <= n-d`,
then `sum_i 2^(k i) <= 2^n`. The finite sum bound uses
`sum_i 2^k <= |V|*2^(n-d) <= 2^d*2^(n-d)=2^n`.

This is a general **sufficient** Kraft-type criterion, not a deduction
from arbitrary `AngleCap` geometry alone.

`planar_eight_centre_no_high_layers_capacity`:
for an actual injective planar `AngleCap p lam` and genuine centre
cycles, `n>=3`, `0<=delta<1/2`, `t=n+delta`,
`lam=pi/t`, `card V<=8`, and no original centre with
exponent `n-1` OR `n-2`, the genuine dyadic capacity bound
holds. The implication from these exclusions to all exponents
`<=n-3` uses the already proved actual geometric lemma
`centreExponent_lt_n`.

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39031141678
**SUCCESS**, 3224 Lake jobs. Both printed axioms
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

A further genuine geometric contrapositive theorem,
`planar_eight_centre_overweight_has_high_layer`,
was subsequently added: if `card V<=8` and the original
capacity is overweight, at least one centre has exponent
`n-1` or `n-2`. It is logically derived from the prior
kernel-verified eight-centre result; its own new focused
run is https://github.com/Charlie-Wang-03/awards/actions/runs/39031460978.
That later focused CI has now been independently verified:
**SUCCESS**, 3224 Lake jobs, the new theorem's printed axioms exactly
`[propext, Classical.choice, Quot.sound]` and NO `sorryAx`.

## C. Sole admitted root further restricted

`PlanarLowerBranchProofAdmittedWIP.lean` imports the
kernel-verified uniform exponent-drop module and adds:

`by_cases huniformDrop :
    exists d : Nat, d<=n and card(ProjectionOrdered V)<=2^d
                and forall i, centreExponent(cycles i) t <= n-d`.

The positive case is DISCHARGED by
`dyadic_capacity_of_uniform_exponent_drop`.
The negative branch retains ALL old genuine six-source liabilities,
including external TRUE holes, non-reuse, NET duplicate debt,
hard/soft/mixed/twin carriers, and projected profile loss.

Exactly ONE executable original WIP `sorry` remains,
at approximately line 715 after this insertion.
This is a strictly wider discharged PROFILE family than merely
the actual eight-centre special case; it does not assert
the profile condition holds for all planar configurations.

Focused root-integration workflows started:
- https://github.com/Charlie-Wang-03/awards/actions/runs/39031330329
- https://github.com/Charlie-Wang-03/awards/actions/runs/39031330314
- https://github.com/Charlie-Wang-03/awards/actions/runs/39031330404

When drafted, these focused runs were still IN PROGRESS.
Only explicitly concluded CI runs may be counted as kernel passes.

## D. Historical Lean repair

File: `JSP000404Research/HiddenLargeAngleTriangle.lean`.
The last completed full-tree diagnostics had SIX errors.
Changes:

- Fixed the `hp.ne hix` argument direction in the triangle sum API.
- Aligned Nat subtraction cast via `Nat.cast_sub` and explicit
  `Nat.cast_one` normalization; rewrote `hpi/ht` only where
  their expressions occur.
- Moved the `{lam t delta : Real}` binder in front of
  `(hcap : AngleCap p lam)` to prevent a distinct shadowed
  `lam` in the downstream physical-angle theorem.

Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39031257365:
**SUCCESS**, 3452 Lake jobs, all THREE printed axioms exactly
`[propext, Classical.choice, Quot.sound]`.
No additional `sorry` and no weakened theorem statements.

## E. Outstanding genuine mathematical question

The complete JSP-000404 statement still requires the
unconditional geometric non-reusing six-source payment into
actual external Boolean TRUE holes plus genuinely unreserved
surplus; these must pay actual retained-edge covered blockers,
mobile/soft terms, reverse rigid and twin/mixed terms, NET
duplicate debt, and projected profile loss. The conditional
profile and geometric finite-cardinality closures above
do not prove or refute that general claim.
