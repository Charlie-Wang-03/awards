# JSP-000404 — Sharp phase certificate and formalization relay (2026-10-23)

## Verified mathematics (focused Lean 4.34 / pinned Mathlib)

* `SixPointHardBranchPositiveGapJointCertificate.lean`: `six_point_uncompensated_top_joint_certificate_of_exact_threshold` is **kernel-checked** in [CI #39954822480](https://github.com/Charlie-Wang-03/awards/actions/runs/39954822480) (9,107/9,107 Lake jobs, `#print axioms` reports `[propext, Classical.choice, Quot.sound]`, no `sorryAx`). It combines an actual separated/non-gaining support-two original-geometry centre with one physical period phase avoiding **all** positive quotient-gap bad intervals, under the exact `14 * delta < (n : ℝ)` bound, `5 <= n`, `0 <= delta < 1/2`, actual six-centre top/minima exponent profile and `SixPointNoCompensatedTopDeletion`.
* `SixPointTwoNonGainers.lean`: `two_nonGaining_lowSupport_witnesses` is independently **built and axiom-audited without `sorryAx`** in [CI #39954845986](https://github.com/Charlie-Wang-03/awards/actions/runs/39954845986), even though that overall focused workflow failed on a **different** module. The result retains two distinct actual non-gaining minima, with either two support-two centres or one support-one and one support-two, with the support-two centre not positive-positive top-pinned.
* `TurnUnitPhaseInterval.lean`: **built** in the same [CI #39954845986](https://github.com/Charlie-Wang-03/awards/actions/runs/39954845986). Its previous failed `rfl` was replaced by the already-proved canonical unit-gap start bridge.

## Latest Lean repair state

* Prior incremental whole research-tree failure [#39951123334](https://github.com/Charlie-Wang-03/awards/actions/runs/39951123334) contained errors in **12 module paths** (the root `PlanarLowerBranchProofAdmittedWIP.lean` remains admitted). Do not confuse a focused PASS with all-tree green.
* `ExactWitnessCanonicalUnitGap.lean` on [focused CI #39955753661](https://github.com/Charlie-Wang-03/awards/actions/runs/39955753661) still failed on two index/append normalization goals. Prior binder/type-mismatch and invalid rewrite issues were reduced, not fully resolved. No successful check for this module is asserted.
* `TurnUnitGapBridge.lean` on [focused CI #39955415443](https://github.com/Charlie-Wang-03/awards/actions/runs/39955415443) reduced to four goals; follow-up source fixes in `6c82792e` are awaiting the independent [focused CI #39956326957](https://github.com/Charlie-Wang-03/awards/actions/runs/39956326957). Do not mark this module PASS without that result.
* The remaining broader compilation issues include `ResidualEnlargedLossDegree`, `ProjectionSaturatedEndpointDichotomy`, `LinearCyclicDeletionGain`, `WeightedHanselSlice`, `SaturatedBandJumpMismatch`, `SixPointMergedTwoExceptionEquality`, `SeparatedSupportTwoResidualBudget`, `CutTriangleCriticalSlot`, and `UncoveredBoundaryColoring`. A clean full-tree compile has NOT been obtained in this relay.
* Focused runner `jsp000404-focused-proof-repairs.yml` was added to avoid mistaking the huge incremental tree's unrelated failures for the result of an individual patch.

## ONE genuinely open mathematical input (do not silently strengthen assumptions)

The executable `sorry` in `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` near line 900 **remains**. The original lower-branch/global theorem is neither proved nor disproved.

What is missing is a GLOBAL, original-geometry, **non-reusing** payment of the exact covered translated-loss blockers, NET duplicate debt, terminal hard/twin/mixed-rigid/soft debts from genuine TRUE Boolean holes outside translated-loss slices and genuinely unreserved dyadic surplus. Covered words, candidate positive-gap slots, and already reserved shell surplus cannot be treated as available hole credit.

The newly proved sharp phase theorem excludes covering all phases by the corresponding canonical positive quotient-gap bad arcs. To turn this into a contradiction, one would need to PROVE (not assume) that failure of the actual non-reusing global resource inequality forces suitably strong original-geometry bad-phase coverage, or find a direct true-hole resource-matching/charging argument. This implication is not established and is not an elementary consequence of the <=14 slot count. In particular the separate `GeometricCertificates` assumption in the independent upstream partial formalization PR #5131 also does NOT discharge this gap.

No additional axiom, `admit`, or executable `sorry` was intentionally added. No upstream complete-proof PR or award claim is justified.
