# JSP-000404 — Actual top / third-layer support-one geometric exclusion

Date: 2026-10-17; research branch `research/jsp-000404-sharp-centre`.

## Mathematical statement

A new non-payment geometric theorem has been added in
`JSP000404Research/ThirdLayerTwoSupportOneExclusion.lean`.

For an arbitrary finite injective planar `AngleCap p lam` configuration,
`n>=5`, `0<=delta<1/2`, `t=n+delta`, `lam=pi/t`,
with genuine original centre projective cycles `C`, assume:

* three pairwise distinct original centres `s,a,b`;
* actual top exponent `centreExponent (C s) t = n-1`;
* exact `centreExponent (C a) t = centreExponent (C b) t = n-3`;
* exact `positiveSupport (centreQuotient (C a) t) =
  positiveSupport (centreQuotient (C b) t) = 1`.

These assumptions contradict true planar geometry.

The actual geometric proof is not a disguised arithmetic profile premise:
`concrete_unit_deficit_is_sharp` derives the genuine sharpness of `s`
from its exact top exponent. The previously independently repaired
`DeficitThreeSupportOneGeometry.lean` then gives two incompatible
bounds on the SAME original angle `angle(p s,p b,p a)`:

`(n-2-delta)*lam <= angle(p s,p b,p a) <= (2+delta)*lam`.

The left inequality uses sharp s and support-one centre a.
The right inequality applies the genuine common-signed interval at b.
Because `n>=5`, `delta<1/2`, `lam>0`,
`2+delta < n-2-delta`. Contradiction.

Thus with a top centre `s`, the number of OTHER actual centres
of exponent `n-3` and quotient support ONE is at most ONE.
No bound on ambient `card V` is assumed, other than finiteness.

The module separates:
1. sharp-centre geometric contradiction;
2. actual top-exponent specialization;
3. finset cardinal multiplicity bound.

## Compilation and proof status

The two previously repaired supporting modules independently passed
CI without `sorryAx`:
- `DeficitThreeSupportOneGeometry.lean`
  https://github.com/Charlie-Wang-03/awards/actions/runs/39034738574
  3249 Lake jobs, all three axioms exactly
  `[propext, Classical.choice, Quot.sound]`.
- `SharpSupportTwoLargeAngle.lean`
  https://github.com/Charlie-Wang-03/awards/actions/runs/39034242777
  3464 Lake jobs, two axioms exactly
  `[propext, Classical.choice, Quot.sound]`.

The first focused run for the NEW module
https://github.com/Charlie-Wang-03/awards/actions/runs/39035364147
compiled the purely geometric sharp-centre theorem with standard
axioms, but failed only because the actual top specialization did not
import the already existing `concrete_unit_deficit_is_sharp`.
This was fixed by importing `NoTopTwoNextMultiplicity`.
The explicit cardinality corollary was then added.
Latest dedicated run:
https://github.com/Charlie-Wang-03/awards/actions/runs/39035606774.
**SUCCESS**, 3495 Lake jobs. All THREE new geometric theorems,
including the actual top-exponent theorem and the genuine finite
third-layer support-one cardinality bound, printed exactly
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

## Existing WIP root, not a full proof

The standalone `SixteenCentreNoTopTwoLayerCountCapacity.lean`
module also passed after a corollary was added:
https://github.com/Charlie-Wang-03/awards/actions/runs/39035152840,
3226 Lake jobs, three theorems with only
`[propext, Classical.choice, Quot.sound]`.

Its two-layer count `m+3r+q<=16` branch had been integrated
into `PlanarLowerBranchProofAdmittedWIP.lean` at commit
`9d7c435b8ccc935f91cd45e41d2e5786fb95e21a`.
The main focused integration
https://github.com/Charlie-Wang-03/awards/actions/runs/39034812381
**SUCCESS**, 3804 Lake jobs, and the external true-hole interface
https://github.com/Charlie-Wang-03/awards/actions/runs/39034812351
also SUCCESS. The root still contains EXACTLY ONE original
executable `sorry` at line 745 after this integration.

The original six-source payment from actual retained hard/soft/twin
carriers and NET duplicate debt into distinct literal TRUE holes
and genuinely UNRESERVED dyadic surplus is NOT closed.
The newly excluded top/third-layer support-one pattern is a
true geometric exclusion, but cannot yet discharge every other
profile or the general six-source allocation.

## Main admitted residual ledger integration

Commit `17129ff3fa838635fbee8bb244622c360be0df30`
imports `ThirdLayerTwoSupportOneExclusion` into the sole WIP
main root and establishes a LOCAL universally quantified
`hthirdSupportOneCountBound` at the remaining six-source frontier.
For any actual top centre and `n>=5`, the count of distinct
other third-layer support-one centres is <=1. This is a real
proved geometric invariant, not a hypothecated hole/soft credit.

The one explicit global six-source `sorry` is still present
(now near line 763). This imported geometric invariant has not
by itself proved global nonreusable TRUE-hole payment. Check the
main-root focused CI independently before describing its newest
insertion as successfully integrated.
