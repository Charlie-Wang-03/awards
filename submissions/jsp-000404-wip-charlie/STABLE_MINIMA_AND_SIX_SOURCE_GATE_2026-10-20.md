# JSP-000404 — 2026-10-20 Lean repair and proof-frontier checkpoint

Status: research WIP only. No full proof or disproof of JSP-000404 is claimed.

## New kernel-checked local proof

File: `JSP000404Research/SecondDeletionTwoStableMinima.lean`.

1. Replaced invalid `Finset.sdiff` projection with Finset difference.
2. Restored the missing definitional link between the minimum-layer card bound and the local finite set `M`; this removed the subsequent `omega` failure.
3. Proved `exists_two_minimum_survivors_with_unchanged_exponents`: with four minimum-layer centres in an exact dyadic child and a bounded monotone second deletion, two surviving minimum-layer exponents are exactly unchanged.
4. Proved the stronger `secondStableMinima_card_add_two_ge_layer_card`: for every bounded monotone second minimum deletion, the number of minimum-layer survivors with no full-unit exponent gain, plus two, is at least the original minimum-layer cardinality. No cardinality-four assumption is required for this quantitative theorem.

CI verification:
- https://github.com/Charlie-Wang-03/awards/actions/runs/39439626886 — SUCCESS (two stable survivors and exact-unchanged extension).
- https://github.com/Charlie-Wang-03/awards/actions/runs/39440782888 — SUCCESS (quantitative all-cardinality refinement).
- The three printed audit axiom families use `[propext, Classical.choice, Quot.sound]` and do not include `sorryAx`.

The gain-count restriction comes from `SecondDeletionSlack.lean` and the exact deleted weight bound; the upgrade from no full-unit gain to exact stability uses integer exponent monotonicity.

## Legacy Lean engineering

- Three stale Mathlib import paths were replaced in `CentreTransitionRefinement.lean`, `CutCentreTransitionRefinement.lean`, and `CyclicBandMissing.lean`. These are engineering repairs, not proofs of the JSP theorem; independent full-file build results must be checked before claiming success.
- `MiddleProjectiveGapDeletion.lean` has an independent focused workflow and staged repairs to missing quotient definitions, noncomputable real-valued definitions, delimiter balance, reserved tactic identifiers, and last-element recurrences. Its latest build must be checked before calling that module verified.
- Existing full-tree Fast Incremental Lean builds have historically failed with unrelated legacy diagnostics. A successful focused module is not a clean full-tree build.

## Still-open mathematical boundary

There is still exactly one intentionally admitted executable `sorry` in
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`. Its scope is not a small syntactic lemma: the unrestricted global six-source planar payment must pay genuinely covered loss carriers, cross-coordinate duplicate debt and the other soft/hard/twin/mixed-rigid debts through **outside true holes plus genuinely unreserved dyadic surplus**, without reusing any payment. The new deletion lemmas do not establish that global allocation.

The underlying historical source-closure audit also remains OPEN; see `SOURCE_CLOSURE_GATE_2026-09-28.md` and `ACTA_1995_PROOF_DEPENDENCY_AUDIT_2026-09-29.md`.

Next mathematical gate: derive a genuinely new global nonreusing allocation or a source-honest counterexample; do not assert the existential payment condition merely because its conditional theorem is Lean-checked.
