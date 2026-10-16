# JSP-000404 — Mixed-exterior geometric closure and Lean repair ledger
Date: 2026-10-16. Branch: `research/jsp-000404-sharp-centre`.

## Mathematical status

The original full arbitrary-cardinality planar lower-branch theorem
`PlanarLowerBranchProofAdmittedWIP.lean` **remains OPEN** and its only
executable `sorry` remains at line 632. This checkpoint does not
prove or disprove the full original JSP-000404 assertion. None of the
repairs below changes the geometric definitions or inserts additional
axioms/admissions. A successful focused build is not a full-workspace
build certificate.

The last inspected broad incremental run,
[38909539500](https://github.com/Charlie-Wang-03/awards/actions/runs/38909539500),
failed with **358 errors in 35 legacy modules** (the preceding observed
baseline had 375 errors in 36 modules). This is a historical census,
not a fresh post-fix count for this checkpoint.

## 1. Newly closed mixed-four-centre exterior geometry branch

File:
`JSP000404Research/FourCentreMixedExteriorShortTurnFrontier.lean`.

A fully kernel-checked Lean proof now composes genuine planar geometry
with the previously certified transition support packing theorem.

- `mixed_four_exterior_strict_exposure_and_short_turn`: if a
  fourth vertex c lies OUTSIDE conv(s,a,b), it is strictly exposed;
  every support-interval certificate at c must have turn < lam,
  **provided** the three high transition certificates have
  quotient cost sum 2*n, normalized t=n+delta, and delta<1/2.
- `mixed_four_fourth_mem_triangle_of_transition_cost`: under
  the actual AngleCap, the four-point exposed-support theorem
  (`ExposedSupportIntervalFinFour.lean`) supplies a true
  support certificate at c with turn >=lam. The preceding strict
  inequality gives a contradiction. Therefore c MUST lie in
  `convexHull ℝ {p s,p a,p b}`.

These are actual Euclidean-plane statements with an injective
`Fin 4 → Plane` configuration, not a model which defines its answer
by the target formula. The theorem's *explicit prerequisites* still
include three `HighExponentTransitionIntervalCertificate` values and
their cost-sum equality; those must be derived from the real
exponent/support branch by other lemmas.

**Focused CI**:
[38913183902](https://github.com/Charlie-Wang-03/awards/actions/runs/38913183902):
**SUCCESS**, 3,459 jobs. Both theorem axiom audits:
`[propext, Classical.choice, Quot.sound]`, NO `sorryAx`.

This eliminates the mixed **exterior** case once its transition
certificate premises are available. It does not eliminate the
**interior** case, arbitrary configurations, or six-source global
payment.

## 2. Targeted geometry and residual Lean repairs certified

| Module | CI | Jobs | Verified repair |
|---|---|---:|---|
| `TwoScaledSmallAngleContradiction.lean` | [38912035756](https://github.com/Charlie-Wang-03/awards/actions/runs/38912035756) | 3264 (shared) | Reuse audited asymmetric triangle theorem; correct AngleCap argument direction |
| `TwoSmallMatchingSharedEdgeContradiction.lean` | same run | 3264 (shared) | Shared matching-edge contradiction, consistent lambda binder |
| `FourPointConvexSeparation.lean` | same run | 3264 (shared) | Explicit real scalar for finite convex hull closedness; strict exposure proved |
| `FourCentreMixedExteriorOutlet.lean` | [38912232454](https://github.com/Charlie-Wang-03/awards/actions/runs/38912232454) | 3442 | Exact support-arc packing arithmetic and corrected certificate specialization |
| `ResidualUnsafeEdgeOrder.lean` | [38912360680](https://github.com/Charlie-Wang-03/awards/actions/runs/38912360680) | 3124 | Deduplicate 170 lines, reuse audited `ResidualThroughDensity` witnesses; preserve all theorem statements |

Every listed scoped declaration has been compiled with no
`sorryAx` in its reported axiom audit. All three CI groups
are independent, with pinned Lean/Mathlib setup and full imports of
their targeted modules.

## 3. Remaining chain to the global theorem

1. **Actual mixed transition data.** Certify that the real
   `centreExponent`/quotient-support assumptions imply the
   high-transition certificates and `qe` cost sum of 2*n.
   The legacy `FourCentreTransitionCases.lean` still has errors
   (dependent Fin3 certificate elimination, missing list-sum helper
   and incorrect scale binding). Its already-authored mixed branch
   cannot be treated as globally checked on that account.
2. **Interior mixed case.** Turn the true
   `c ∈ convexHull {s,a,b}` conclusion into the exact mixed
   interior geometric inequalities and the certified linear
   contradiction in `FourCentreMixedInteriorArithmetic.lean`.
3. **Beyond four centres and all debt sources.** None of the
   mixed-centre geometry supplies global, non-reusing payment by
   true outside Boolean holes and *unreserved* dyadic surplus for
   the soft, forward/reverse hard, TWIN, both mixed-rigid,
   and projected-profile-loss debt families.
4. **Global Lean hygiene.** Reduce the outstanding legacy
   compilation failures and re-run the broad incremental/full
   module build. A single remaining executable root `sorry`
   is not itself evidence of mathematical closeness to a full
   proof; its global inequality remains substantive.

## 4. Scope and integrity

This checkpoint records successful proofs and their **conditional**
premises, not an award submission or claim of completeness.
Do not replace Blumenthal's plane minimax definition by Sendov's
closed-form expression, introduce `axiom`, or count already
covered words as new true holes. All global nonreuse obligations
remain explicit.
