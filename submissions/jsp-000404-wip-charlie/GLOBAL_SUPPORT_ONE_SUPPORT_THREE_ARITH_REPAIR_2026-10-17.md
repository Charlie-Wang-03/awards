# JSP-000404: global second-layer support-one, sharp-pinned third layer, four-term arithmetic

Date: 2026-10-17
Branch: `research/jsp-000404-sharp-centre`
Repository: `Charlie-Wang-03/awards`

## Verified new global planar spectrum restriction

Module `JSP000404Research/GlobalSecondLayerSupportOneMultiplicity.lean`:

- `actual_secondLayer_supportOne_card_le_two`:
  For an arbitrary finite injective planar configuration under original
  `AngleCap`, `n >= 4`, `0 <= delta < 1/2`, `t=n+delta`,
  `lambda=pi/t`, at most **two** actual centres with exponent
  `n-2` can have positive quotient support exactly one.
- `ProjectionOrdered.projection_secondLayer_supportOne_card_le_two`:
  the same actual geometric statement, with exactly the projection
  reindexing and cycles used by the original global lower-branch proof.
- Uses the existing actual three-centre transition packing obstruction,
  and converts no-three-centres into the genuine finite-set cardinal
  bound using `Finset.two_lt_card_iff`.
- CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39005354367
  **SUCCESS**, 3,495 Lake build tasks.
- Both exported theorems: `#print axioms` =
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

This holds whether or not a top centre exists. It restricts the
number of support-one second-layer centres; it does NOT bound the
entire second layer by two, since support-two centres remain possible.

## Verified genuinely geometric support-three pinned cycle

Module `JSP000404Research/SharpPinnedSupportThreeShape.lean`:

- Restores `exists_sharp_pinned_support_three_shape_with_split` and
  `exists_sharp_pinned_support_three_shape`.
- For a sharp ray and a genuine deficit-three/support-three centre,
  cyclically pinning the ray shows both adjacent quotient gaps are
  strictly positive; the remaining interior block has **exactly one**
  positive quotient; all other interior gaps have quotient zero,
  and the actual-angle zero-mass stays at most `delta*lambda`.
- Fixes the scale lemma, dependent match-branch equalities,
  cyclic list lengths, explicit end-ray last-element membership,
  cyclic angle-list wrap equality and middle positive support proof.
- CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39005410389
  **SUCCESS**, 3,244 Lake build tasks.
- Both target axiom audits: only the three standard Lean axioms,
  no `sorryAx`.

The result is a real structural input on the `n-3` layer, not a
global full capacity proof.

## Verified repaired four-centre dyadic arithmetic

Module `JSP000404Research/FourCentreArithmetic.lean`:

- Restores `four_dyadic_terms_le_of_sharp_structure`:
  if all four `k_i<n`, the top `n-1` occurs at most once,
  and when it occurs the next layer `n-2` occurs at most once,
  then `sum_i 2^(k_i) <= 2^n`.
- Pointwise instances of `hk : forall i, k_i < n` are provided
  explicitly for `omega`; the four dyadic-doubling steps use a
  multiplication bridge before rewriting `pow_succ`.
- CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39005596503
  **SUCCESS**, 3,249 Lake build tasks.
- Axiom audit contains no `sorryAx`.

## Additional research-only Lean repair pending certificate

`JSP000404Research/ListCyclicSupportBridge.lean` was updated to
explicitly transport between `Fin C.gaps.length` and
`Fin (quotientList t C.gaps).length` using the proved
`quotientList_length`; these index types must NOT be treated as
definitionally identical. Also corrects the `centreQuotient_ofFn`
rewrite direction and cyclic wrap rotation normalization.

Focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39005753781

**At document authoring time this last fix is PENDING Lean certification.**
No PASS assertion is made here until GitHub Actions completes.

## Precisely remaining original problem

`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` still
contains the unique executable `sorry` at the genuine net
six-source payment input. The remaining original planar problem
is to prove the unrestricted, globally non-reusing bound:

  six-source terminal debt + genuinely covered translated-loss
  blockers + cross-coordinate duplicate hits
  <= true Boolean holes OUTSIDE translated-loss union
     + genuinely unreserved dyadic profile surplus.

This is NOT proved by the new top-layer multiplicity, support-one
second-layer bound, pinned support-three structure, or four-term
arithmetic. Covered sink words are not true holes; already reserved
strict-rigid lower shell mass cannot be recycled as surplus.
The research branch remains a WIP, not a solved JSP-000404 entry.

Legacy broad incremental Lean CI remains separate from named
focused-module success; previous broad run(s) were either failed
for other historical modules or cancelled by branch concurrency.
Only individual focused CI certifies the named results.
