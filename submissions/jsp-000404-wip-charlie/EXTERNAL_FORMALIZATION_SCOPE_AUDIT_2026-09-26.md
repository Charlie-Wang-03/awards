# JSP-000404 external formalization scope audit — 2026-09-26

## Purpose

This note records a scope check of newly visible upstream Lean submissions for
JSP-000404.  It is a research audit only.  It does not make any award,
priority, or maintainer-status claim.

## PR #2751

Upstream PR #2751 does not formalize the Blumenthal/Sendov extremal problem.
Its submitted Lean diff consists of elementary unrelated arithmetic and
primality facts about the integer 404.  The upstream maintainer discussion also
states that the submission provides only partial progress and does not meet the
complete-solution requirement.

Conclusion: **not a complete formalization of JSP-000404**.

## PR #2804 / Yi-111-a

Pinned source inspected:

- repository: `Yi-111-a/jsp-000404-blumenthal-sendov`
- commit: `f7bf2cce3bd37fec9f1bce2d04c47b8b88c88061`
- headline theorem: `sendov_minimax_angle`

The critical issue is statement origin.

In `lean/JSP404/Defs.lean`, the quantity

`alpha (N : ℕ) : ℝ`

is **defined directly by Sendov's target piecewise formula**, using
`Nat.clog 2 N` and the two desired closed forms.  It is not defined as the
Blumenthal extremal quantity over finite planar configurations and Euclidean
angles.

Consequently `lean/JSP404/Main.lean` proves
`sendov_minimax_angle` by:

1. identifying `Nat.clog 2 N = n` in the relevant dyadic interval;
2. unfolding the formula-defined `alpha`;
3. selecting the corresponding branch of the defining `if`.

This proves that the function defined to equal Sendov's formula satisfies
Sendov's formula.  It does **not** prove that the geometric extremal quantity

> the largest angle that every planar set of N points must determine

equals that formula.

The repository's own README at the pinned commit still describes the project
as WIP / PARTIAL and says the headline was originally a scaffold.  Regardless
of whether the current theorem contains `sorry`, the statement-definition
mismatch is already sufficient to prevent it from serving as a complete
formalization of the original geometric problem.

Conclusion: **the pinned #2804 source does not replace the missing geometric
lower-bound proof and does not close the present downstream research gap**.

## Consequence for this branch

Continue the independent geometric proof route.

The current downstream branch defines and proves actual Euclidean/projective
geometry, centre quotient profiles, deletion monotonicity, exact-normalization
preservation, residual/projective-band capacity reductions, and weighted
repair interfaces.  The remaining work must continue to connect those genuine
geometric objects to the sharp arbitrary-cardinality capacity bound.

No claim of first formalization or award priority is made here.
