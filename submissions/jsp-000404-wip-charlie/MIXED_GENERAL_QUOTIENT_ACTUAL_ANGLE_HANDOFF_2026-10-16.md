# JSP-000404 — Arbitrary-cardinality mixed-centre actual-angle checkpoint

Date: 2026-10-16. Research branch:
`research/jsp-000404-sharp-centre`.

## Mathematical scope

These results use the genuine finite ordered vertex set, injective
`p : V → Plane`, geometric `AngleCap p lam`, normalized
`t = n + delta`, `0 ≤ delta < 1/2`, `n ≥ 3`, and the
original centre exponent / quotient-support data

```text
centreExponent Cs t = n-1
centreExponent Ca t = n-2
centreExponent Cb t = n-2
positiveSupport (centreQuotient Ca t) = 1
positiveSupport (centreQuotient Cb t) = 2
```

for three pairwise distinct original centres `s,a,b`.

The original global planar lower-branch dyadic capacity theorem
**remains OPEN**. It still has one executable `sorry` in
`PlanarLowerBranchProofAdmittedWIP.lean` around line 632, the
non-reusing payment by true Boolean holes outside translated loss
and unreserved surplus across six source families.
This checkpoint neither changes that statement nor removes that
`sorry`. No custom `axiom`, `admit`, or replacement definition
of the target minimax quantity was introduced.

## Independently verified results

1. **Cardinality-free mixed interior contradiction**:
   `GeneralMixedInteriorContradiction.lean` — theorem
   `no_mixed_fourth_inside_of_weakened_hidden_angle`.
   Under triangle hull membership and
   `((n-1)-delta)*lam ≤ angle(s,b,c)`, the genuine AngleCap
   geometry and interior angle splitting produce `False`.
   [CI 38927238022](https://github.com/Charlie-Wang-03/awards/actions/runs/38927238022):
   **SUCCESS, 3,226 jobs**, standard Lean axioms only.

2. **Arbitrary-cardinality strict mixed hidden-angle upper bound**:
   `GeneralMixedHiddenAngleFrontier.lean` — theorem
   `general_mixed_hidden_angle_strict_upper`.
   For every fourth original vertex `c` distinct from `s,a,b`,
   the true mixed-centre hypotheses force

   ```text
   angle(s,b,c) < (((n-1):Nat):Real - delta)*lam.
   ```

   This composes the previously checked arbitrary-cardinality
   exterior hull conclusion with the conditional interior terminal.
   The converse matching lower bound excludes the same pattern.
   [CI 38927447049](https://github.com/Charlie-Wang-03/awards/actions/runs/38927447049):
   **SUCCESS, 3,470 jobs**, both declarations no `sorryAx`.

3. **Same-sign quotient arithmetic and small-pair incidence**:
   `HiddenSameSignQuotient.lean`,
   `TwoBadSmallPairIncidence.lean`.
   The hidden `n-1` value in a support-two/unit-transition
   decomposition is on a same-sign step; the crossing small
   pair contradictions retain a consistent AngleCap scale.
   [CI 38927688989](https://github.com/Charlie-Wang-03/awards/actions/runs/38927688989):
   **SUCCESS, 3,449 jobs**, no `sorryAx`.

4. **Authentic general transition quotient = 1**:
   `GeneralMixedTransitionWitness.lean` — theorem
   `general_mixed_transition_decomposition_qe_eq_one`,
   obtained from original `s,a,b` exponents,
   support-one at `a`, and the exact ray/sign transition
   decomposition at `b`, in any finite configuration.
   [CI 38928078811](https://github.com/Charlie-Wang-03/awards/actions/runs/38928078811):
   **SUCCESS, 3,445 jobs**, no `sorryAx`.

5. **General quotient-to-actual-angle bridge**:
   `GeneralNontransitionPayment.lean` proves that an
   arbitrary same-sign quotient occurrence at a centre
   pays `q*lam ≤ angle(x,i,y)` for genuine other vertices;
   this covers both ordinary sorted gaps and the cyclic wrap.
   The support-two/unit-transition large-angle specialization
   is also audited. [CI 38928912816](https://github.com/Charlie-Wang-03/awards/actions/runs/38928912816):
   **SUCCESS, 3,451 jobs**, no `sorryAx`.

6. **Actual large-angle existence under original mixed data**:
   `GeneralMixedLargeAngleWitness.lean` — theorem
   `general_mixed_actual_large_angle_exists`.
   Genuine mixed-centre data force distinct other original
   vertices `x,y ≠ b` with

   ```text
   ((n-1):Real)*lam ≤ angle(x,b,y).
   ```

   [CI 38928912787](https://github.com/Charlie-Wang-03/awards/actions/runs/38928912787):
   **SUCCESS, 3,453 jobs**, no `sorryAx`.

7. **Sharp endpoint restriction**:
   `GeneralMixedLargeAngleEndpointRestriction.lean` —
   theorem `general_mixed_large_angle_sharp_endpoint_forces_support_one`.
   If a genuine large pair has `x=s`, its opposite endpoint
   must be `y=a`; other distinct fourth vertices are forbidden
   by the strict hidden-angle upper bound.
   [CI 38929122977](https://github.com/Charlie-Wang-03/awards/actions/runs/38929122977):
   **SUCCESS, 3,471 jobs**, no `sorryAx`.

## Direct witness classification check

`GeneralMixedLargeAngleEndpointClassification.lean` combines the
authentic existential witness from item 6 with item 7, giving a
three-way choice: both endpoints avoid `s`, or the pair is
`s,a` / `a,s`. This is a combination lemma, NOT
an independent geometric impossibility theorem.

Focused run:
[38929417377](https://github.com/Charlie-Wang-03/awards/actions/runs/38929417377):
**SUCCESS, 3,477 jobs**. The combined theorem's kernel axiom
audit is exactly `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`. This is an honest original-vertex witness
trichotomy, not a proof that either survivor is impossible.

## Remaining mathematical barrier

Even when the general mixed-centre hypotheses force an actual large
pair, the pair's endpoints have not been proved to include the sharp
centre. If BOTH endpoints avoid `s`, the strict upper-bound theorem
alone does not contradict their actual angle. If the large pair is
`s,a`, an additional geometric incidence/angle exclusion is needed.

Moreover, excluding this one local mixed pattern would STILL not
supply the arbitrary-cardinality, globally non-reusing
six-source external-hole and net-unreserved-surplus payment at the
original root `sorry`.

The latest observed broad incremental baseline
[38924708823](https://github.com/Charlie-Wang-03/awards/actions/runs/38924708823)
failed with 337 Lean errors across 34 legacy modules. That
historical count is not a fresh census after the above scoped
repairs, and targeted PASS runs cannot be used to assert an
all-module green build.
