# JSP-000404 — 2026-10-23 GitHub connector proof relay

## Scope

This is a research-only checkpoint. The full original JSP-000404 problem has
**not** been proved or disproved. In particular,
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` still contains one
executable `sorry` for an unproved global geometric/net Boolean-hole payment.
It is kernel-equivalent to the actual outstanding lower-branch obligation and
must not be replaced by an extra hypothesis, a custom axiom, or an unverifiable
counting assumption.

## Independently verified focused repairs

1. **Cyclic concrete transition slots, top deletion compensation.**
   `CyclicTransitionUnitGapSlot.lean` and `SixPointMixedTopDeletion.lean`
   build together. Noncomputability, classical finite-subtype elaboration,
   missing list lemma, and conflicting decidable equality instances repaired.
   Run: https://github.com/Charlie-Wang-03/awards/actions/runs/39903465226
   Conclusion: success, 9,085 Lake jobs. Their printed audited theorems have
   no `sorryAx`.
2. **Six-centre, support-three small perfect matching/Hamiltonian reduction.**
   `MixedSupportThreeSmallMatchings.lean` builds, with its geometric
   two-centre partner obstruction and finite residual classification.
   Run: https://github.com/Charlie-Wang-03/awards/actions/runs/39904274829
   Conclusion: success, 3,555 Lake jobs. No `sorryAx` in its theorem audits.
3. **Actual same-sign versus ordinary-transition unit slots.**
   `TransitionSameSignDisjoint.lean` builds following proof-safe
   `getElem?` / `List.getElem?_eq_getElem` transport in dependent list
   indexing. Both local and global mutual-exclusion theorems have no
   `sorryAx`.
   Run: https://github.com/Charlie-Wang-03/awards/actions/runs/39904724568
   Conclusion: success, 9,062 Lake jobs.

## Further code submitted; do not classify as kernel-verified without CI

* `SixPointNFourOrdinaryTransitionNoCover.lean` strengthens the conditional
  six-centre n=4 cover-exclusion theorem: the phase-dependent obstruction
  predicate `A u x` is preserved. Assuming a genuinely transition-supported
  obstruction predicate and the explicit quantitative cover lower bound, the
  older `hSameUnusable` hypothesis follows from the verified disjointness
  lemma. This **does not prove** the quantitative cover lower bound.
  Focused run: https://github.com/Charlie-Wang-03/awards/actions/runs/39905049047
* `SixPointMixedHamiltonianBaseTriangleTerminal.lean` composes the verified
  support-three matching reduction with the verified Hamiltonian
  base-triangle squeeze. Expected necessary inequalities are:
  `(1 - 2*delta)*lam <= angle(c,b,z)`,
  `(1 - 2*delta)*lam <= angle(b,c,z)`, and
  `angle(b,z,c) <= pi - 2*(1 - 2*delta)*lam`.
  These inequalities do not by themselves contradict AngleCap.
  Focused run: https://github.com/Charlie-Wang-03/awards/actions/runs/39905188427

The above last two results require reading their completed workflow logs before
claiming that their proofs are kernel-verified. A successful focused check
does not imply that the full `JSP000404Research` import tree builds.

## Further repair of root imports

Two nonexistent experimental module imports were removed from
`JSP000404Research.lean`:
`CutSupportThreeBadSameBandAngle` and
`CutSupportOneBadConsecutivePalette`. The independently verified
`SixPointMixedTopDeletion` module was added as an explicit root import.
Other legacy full-tree compilation errors may remain. This is not a green
whole-tree claim.

## The genuine remaining mathematical problem

The root `sorry` is the unpaid **global six-source** ledger: covered
translated-loss blockers, surviving hard/twin and mixed-rigid debt, duplicate
source/image overlap, and projected-loss corrections must be globally charged
against TRUE Boolean holes outside the translated-loss slices plus genuinely
unreserved dyadic surplus. Non-reusing injections, matching capacities and
local geometric obstructions have been proved, but none yet establishes this
global allocation for all planar configurations.

No upstream complete-proof PR, archive, priority claim or award claim is
justified by this checkpoint.
