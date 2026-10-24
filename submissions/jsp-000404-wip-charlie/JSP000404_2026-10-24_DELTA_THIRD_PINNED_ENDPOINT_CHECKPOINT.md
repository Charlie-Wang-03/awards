# JSP-000404 — sharp-endpoint exclusion at δ < 1/3 (2026-10-24)

## Scope

Downstream research-only, **not** a proof or disproof of original JSP-000404.
Branch: `research/jsp-000404-sharp-centre`.

The new theorem `separated_support_two_has_positive_top_endpoint_of_delta_lt_third`
is stated for the original injective planar configuration satisfying `AngleCap`,
a six-centre projective cycle family, a sharp top of exponent `n-1`,
a separated support-two centre of exponent `n-3`, `n >= 5`, and
`0 <= delta < 1/3` (hence `delta < 1/2`).

It produces one **actual rotated ray/quotient witness** with precisely
one zero and one strictly positive top-adjacent quotient-gap endpoint.

## Mathematical proof

If both top-adjacent quotient gaps were zero, let their actual angles be
`A_first, A_last`. The previously certified sharp-top outer-angle
bounds give each at least `(1-delta)*lambda`. The original exact
deficit-three/support-two zero-angle mass budget, after simultaneous
rotation of actual angles and quotient gaps, gives

```text
A_first + A_last + nonnegative_middle_zero_angle_mass
    <= (1+delta)*lambda.
```

Thus `2*(1-delta) <= 1+delta`, requiring `delta >= 1/3`.
For `delta < 1/3` this is impossible. The already proved
`Not TopPinnedPositivePair` separately excludes both endpoint
quotients being positive; naturals are either zero or positive.
Hence exactly one endpoint has positive quotient.

The real source `JSP000404Research/SeparatedSupportTwoResidualBudget.lean`
contains this constructive witness theorem, with no new `axiom`, `admit`
or `sorry`.

## Verification

Focused Lake check: https://github.com/Charlie-Wang-03/awards/actions/runs/40059655177

- **PASS**: 3,551 Lake jobs.
- `#print axioms separated_support_two_has_positive_top_endpoint_of_delta_lt_third`
  returns exactly `[propext, Classical.choice, Quot.sound]`.
- Root import added to `JSP000404Research.lean` for umbrella inclusion.
  A successful focused CI is **not** a green entire research-tree build.

## Exact unresolved boundary

This excludes the simultaneous-zero endpoint motif only when
`delta < 1/3`; the complementary range `1/3 <= delta < 1/2`
remains. Under double-zero endpoints, the same inequalities yield the
necessary sharper bound `middle_zero_angle_mass <= (3*delta-1)*lambda`.
That quantitative residual inequality is currently a paper-level
deduction, **not an additional Lean-certified theorem**.

Most importantly, the single executable `sorry` in
`PlanarLowerBranchProofAdmittedWIP.lean` remains the genuinely open
global, non-reusing six-source payment from true holes *outside*
translated loss slices and genuinely unreserved dyadic surplus.
Covered blockers, NET duplicates, twins, mixed-rigid and projected-loss
debts are not paid by this local geometric result.

No complete proof, upstream solution PR, award claim or new priority
claim is warranted.
