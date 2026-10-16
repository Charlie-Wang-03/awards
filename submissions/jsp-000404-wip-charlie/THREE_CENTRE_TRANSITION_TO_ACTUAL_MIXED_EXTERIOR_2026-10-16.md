# JSP-000404 — Three-centre transition and actual mixed-exterior closure

Date: 2026-10-16. Research branch: `research/jsp-000404-sharp-centre`.

## Status and integrity

The general planar lower-branch theorem is NOT fully proved.
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
still contains one executable `sorry` in the non-reusing global
payment, around line 632. Neither proof here supplies the missing
outside true Boolean holes or unreserved dyadic surplus. No
`axiom`, `admit`, or new `sorry` was inserted.

## 1. Fully repaired three-centre transition classifications

File: `JSP000404Research/FourCentreTransitionCases.lean`.

Focused workflow
[38915833526](https://github.com/Charlie-Wang-03/awards/actions/runs/38915833526):
**SUCCESS**, 3,443 jobs. All six `#print axioms` reports contain
only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

Real work done:
* Replaced the dependent `Fin 3` construction for
  `CentreProjectiveCycle` and transition certificates with exhaustive
  equality cases that reduce definitionally without `Eq.mpr`.
* Fixed accidental shadowing of the normalized real scale `t`
  across three theorem signatures.
* Added a missing proof that zero positive quotients imply zero sum;
  rederived the singleton-positive and two-positive-list support
  arithmetic constructively without the faulty old induction.
* Normalized the finite sum association rather than changing
  the bound or weakening mathematical hypotheses.

Kernel-checked results include
`three_transition_quotient_sum_le_two_n`,
`no_sharp_with_two_support_one_deficit_two`,
`mixed_deficit_two_transition_qe_eq_one` and
`mixed_support_two_has_hidden_n_sub_one`.

In particular, the mixed sharp + support-one + support-two
configuration forces the high transition costs
`n`, `n-1`, and `1`. Their sum is exactly `2*n`;
the support-two centre also has a distinct positive quotient
`n-1` in the original quotient list. This is derived from
original centre exponent and support assumptions, not from a
hypothesis inventing the high-transition costs.

## 2. Certified original-centre mixed-exterior contradiction

File:
`JSP000404Research/FourCentreMixedExteriorContradiction.lean`.

Focused workflow:
[38916312697](https://github.com/Charlie-Wang-03/awards/actions/runs/38916312697):
**SUCCESS**, 3,462 jobs.

`no_mixed_fourth_outside_triangle_fin_four` depends only on
`[propext, Classical.choice, Quot.sound]` and has NO `sorryAx`.

Its original statement begins from a real injective
`Fin 4 → Plane` configuration satisfying genuine `AngleCap`,
the normalized `t=n+delta`, `delta<1/2`, and centre data:

```text
centreExponent Cs t = n-1
centreExponent Ca t = n-2
centreExponent Cb t = n-2
positiveSupport (centreQuotient Ca t) = 1
positiveSupport (centreQuotient Cb t) = 2
```

The theorem excludes a fourth centre outside the triangle
`convexHull ℝ {p s,p a,p b}`. It uses the certified transition
costs from Section 1, strict convex separation, the
exposed-four-point quantitative support interval, and global
`2*pi` support-arc packing. No caller-supplied transition
certificate or cost-sum assumption is required.

The proof fixed the `AngleCap` lambda binder and eliminated
two obsolete `omega` commands after `rw` had already solved
their goals.

## 3. Direct hull-facing interface — kernel verified

New file:
`JSP000404Research/FourCentreMixedExteriorActualHull.lean`,
theorem
`mixed_fourth_mem_triangle_of_actual_sharp_support_pattern`.

This is intentionally a direct positive logical reformulation of
Section 2, exposing the convex hull conclusion to the mixed
interior branch. It is NOT a mathematically independent exclusion
theorem or additional solution to the six-source payment.

Its focused CI:
[38916707659](https://github.com/Charlie-Wang-03/awards/actions/runs/38916707659)
**SUCCESS**, 3,463 jobs. The headline theorem's axiom report contains
only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
This is a verified, positive hull-membership interface that retains
exactly the original exponent/support hypotheses of Section 2.

## 4. Open mathematical and engineering frontier

* **Four-centre interior:** the fourth centre is now forced into
  the triangle of the three distinguished centres. The exact
  hidden support-two quotient-to-angle bridge in
  `FourCentreMixedInteriorHiddenAngle.lean` and the angle-split
  geometry dependency `TriangleConvexCone.lean` still need
  Lean error repair and verification. The short arithmetic
  contradiction by itself is conditional on those geometric
  inequalities.
* **Global:** arbitrary-cardinality six-source true-hole and
  NET unreserved-surplus nonreuse payment remains the sole
  original root `sorry`, not resolved by four-point geometry.
* **Full build:** the broad incremental workflow is separate
  from the focused successful checks and must not be reported
  green until it actually passes. The last confirmed broad
  baseline had 342 errors on 2026-10-16 (before this round);
  follow-up CI must be checked for an updated count.

These are evidence-based boundaries, not assumptions for
an award claim.
