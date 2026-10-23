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

## 2026-10-23 additional verified continuation

The following results are now **independently kernel checked** and should
supersede the corresponding earlier "waiting" items above:

1. `TurnUnitGapBridge.lean` successfully compiled in [focused CI #39957963427](https://github.com/Charlie-Wang-03/awards/actions/runs/39957963427). Its ordinary and wrap dependent turn-unit constructors and scaled-gap equalities now elaborate without Lean errors; the checked exported constructor and start theorems do not report `sorryAx`.
2. `SixPointThirteenSlotAlternative.lean` successfully compiled in [focused CI #39959171500](https://github.com/Charlie-Wang-03/awards/actions/runs/39959171500), with `#print axioms` for `six_point_positive_gap_card_le_thirteen_of_support_one_two` and `six_point_hard_top_thirteen_slots_or_two_support_two` listing only `propext`, `Classical.choice`, `Quot.sound`. The ORIGINAL six-centre no-compensation top profile admits either `Fintype.card (GlobalPositiveGapSlot C t) <= 13` or two distinct non-gaining support-two minima. The 13 budget is proved by the explicit 1+1+2+3+3+3 support decomposition. This does not improve the existing fifteen-phase threshold without a separate phase argument.
3. `LinearCyclicDeletionGain.lean` successfully compiled in [focused CI #39960741070](https://github.com/Charlie-Wang-03/awards/actions/runs/39960741070) (3,217/3,217 Lake jobs). `listExponent_linearCyclic_delete_second_gain` and `listExponent_linearCyclic_delete_last_gain` both report no `sorryAx`. This repairs the physical list-gap floor-merge/carry backends for cyclic deletion.
4. `ExactWitnessCanonicalUnitGap.lean` was found to trigger an unrelated import-environment collision when simultaneously importing `TurnUnitGapBridge` and `ExactWitnessUnitGapMass`: duplicate generated `positiveIndexSet.eq_1`. The heavy-bridge import was therefore REVERTED from this file. A direct, lightweight `getElem` proof with explicit index bounds is under focused CI. **Do not label this last module verified until its own CI succeeds.**

The only executable top-level research proof hole is still the one in
`PlanarLowerBranchProofAdmittedWIP.lean`. The sharpened six-point
geometric support and phase lemmas, like all structural partial results,
do not yet provide the exact non-reusing global TRUE Boolean-hole and
unreserved-dyadic-surplus payment needed to close this hole. All-tree
compilation is NOT asserted by these focused checks.


## 2026-10-23 second continuation — additional kernel-checked work

### Local Lean repairs

* `LinearCyclicDeletionGain.lean`: a helper theorem named
  `successiveDiffsFrom_append_cons` collided with a generated declaration
  from `ProjectiveCutRotation` when the entire changed-module tree loaded.
  It has been renamed to `successiveDiffsFrom_append_last_linearCyclic`.
  The module was independently rechecked in
  [run #39966584594](https://github.com/Charlie-Wang-03/awards/actions/runs/39966584594) — PASS, not merely syntax reviewed.
* `CyclicFiniteSampling.lean`: [run #39966920889](https://github.com/Charlie-Wang-03/awards/actions/runs/39966920889)
  — PASS, all 9,079 Lake jobs. Fixes: explicit noncomputability of real
  periodic samples, signed difference cast proofs, redundant tactic after
  a finished goal, and correct sign of the wrapped absolute difference.
  `cyclicSamplePhase_injective_on_same_anyBaseArc` uses no `sorryAx`.

### Mathematically stronger original-geometry local result

* `PositiveGapThirteenSlotPhase.lean`: [run #39967310330](https://github.com/Charlie-Wang-03/awards/actions/runs/39967310330)
  — PASS, 9,108/9,108 targets, all three printed theorems have only
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
  * `positive_gap_safe_sample_of_card_lt`: any strictly fewer than
    `M` canonical positive-gap bad slots cannot obstruct all `M` equally
    spaced physical phases when `M≥2`, `0≤delta<t/M`.
  * `six_point_support_one_two_safe_fourteenPhase_of_threshold`: under
    genuine six-centre top/minima exponents and a support-one/support-two
    pair, there exists one safe period phase if `13*delta<n`
    (equivalently `14*delta<t`). Hence for `n=6` the corresponding
    subbranch is proved for `delta<6/13` rather than `delta<3/7`.
  * `six_point_hard_top_two_support_two_or_safe_fourteenPhase`: original
    `AngleCap` + uncompensated top deletion imply either **two distinct
    non-gaining support-two** minima, or the above safe phase.

**Critical logical limitation:** no proof that a GLOBAL shortage of true
Boolean holes and unreserved dyadic surplus forces a cover by the above
positive-gap arcs. Thus a safe phase alone cannot discharge the original
nonreusing payment inequality or the executable `sorry` in
`PlanarLowerBranchProofAdmittedWIP.lean`.

### Not yet verified

* `ExactWitnessCanonicalUnitGap.lean`: its earlier raw `getElem` proof
  did not compile because a dependent `Fin` proof failed to transport
  across the definition of `C.gaps`. The source has been revised to
  introduce the intermediate `hgap` statement with ordinary
  `C.gaps[m]` notation, following the successful `TurnUnitGapBridge`
  proof pattern. The focused result at this checkpoint is still
  **PENDING**, not green.
* Full changed-module tree: numerous unrelated Lean errors remain;
  don't mark the entire research tree compilable based on focused PASS.


## 2026-10-23 third continuation — exact-witness and saturated mismatch closure

**Kernel-verified outcomes (all are downstream partial results; NOT the global theorem):**

1. [Focused run #39968483780](https://github.com/Charlie-Wang-03/awards/actions/runs/39968483780): SUCCESS, 9,124/9,124 jobs. `ExactWitnessCanonicalUnitGap.lean` now compiles. The following three `#print axioms` outputs contain precisely `[propext, Classical.choice, Quot.sound]`, no `sorryAx`: `centre_gap_get_adjacent_eq`, `centre_gap_get_wrap_eq`, `exists_exactWitness_canonical_unit_gap`. One *same* canonical `e : Fin C.gaps.length` simultaneously satisfies `centreQuotient C t e = 1` and `t * C.gaps.get e = 1`.
2. [Focused run #39971176608](https://github.com/Charlie-Wang-03/awards/actions/runs/39971176608): SUCCESS, 3,214/3,214 jobs. `SaturatedBandJumpMismatch.lean` has been repaired: exact exponent componentwise equality, zero-positive mismatch counting, positive-support difference identity. All four printed lemmas have axioms `[propext, Quot.sound]` without `sorryAx`. The two inter-list `Fin` positions must be related using `Fin.ext` rather than direct rewriting of dependent evidence.
3. [Focused run #39966584594](https://github.com/Charlie-Wang-03/awards/actions/runs/39966584594): renamed `successiveDiffsFrom_append_cons` to `successiveDiffsFrom_append_last_linearCyclic`, eliminating a *real* duplicate-declaration import collision with `ProjectiveCutRotation`. The repaired cyclic-deletion module builds.
4. Previously established [run #39967310330](https://github.com/Charlie-Wang-03/awards/actions/runs/39967310330) remains the sharp six-centre support-one/two phase result at `13*delta < n`, and [run #39966920889](https://github.com/Charlie-Wang-03/awards/actions/runs/39966920889) is the general periodic sample lemma.

**Additional code repair still pending CI at this checkpoint:** `UncoveredBoundaryColoring.lean` corrected `lam` binder order, exact Fin band transports, and the noncomputable boundary Boolean bit's classical `if`. `CutTriangleCriticalSlot.lean` corrected parity replacement (matching the already-verified unspecialized triangle parity proof), lambda scope, and explicit reversal of normalized edge coordinates. Do not report either as verified without its independent focused CI success.

**Main mathematical status:** `PlanarLowerBranchProofAdmittedWIP.lean` still has its intentional genuine terminal `sorry`. The exact global non-reusing TRUE Boolean-hole / unreserved dyadic payment inequality is NOT proved. A checked safe phase, a bounded positive gap slot count, exact-witness unit slot geometry, or quotient/band-jump equality DO NOT imply that global payment. The missing geometric implication from nonpayment to exhaustive bad-phase coverage is also not established. Some historical conditional lemmas are logical reductions rather than independent solutions. Full research-tree compilation remains separate and unverified.


## 2026-10-23 fourth continuation — stronger full-delta-arc phase certificate

**NEW KERNEL-CHECKED RESULTS:**

* [CI #39971090898](https://github.com/Charlie-Wang-03/awards/actions/runs/39971090898): `CutTriangleCriticalSlot.lean` PASS, 9,076 targets. The original short-cut triangle implies an actual cyclic critical unit-gap obstruction. `#print axioms` excludes `sorryAx`.
* [CI #39971468022](https://github.com/Charlie-Wang-03/awards/actions/runs/39971468022): `UncoveredBoundaryColoring.lean` PASS, 9,077 targets. At a cut phase free of critical unit-gap obstructions, `cutBoundaryWrapBit_separates` produces an actual boundary-edge separating Boolean bit. `#print axioms` excludes `sorryAx`.
* [CI #39972800339](https://github.com/Charlie-Wang-03/awards/actions/runs/39972800339): `PositiveGapFullDeltaArcEscape.lean` PASS, 9,109 targets. `positive_gap_exists_full_deltaArc_free_sample` is strictly STRONGER than avoiding physical positive bad subintervals: when `card(GlobalPositiveGapSlot C t) < M` and `0 <= delta < t/M`, some equally spaced physical phase avoids the ENTIRE full-width periodic delta arc `[alpha_u+k*t,alpha_u+k*t+delta]` for every actual canonical positive quotient gap. Axioms exactly `[propext, Classical.choice, Quot.sound]`.
* [CI #39972953795](https://github.com/Charlie-Wang-03/awards/actions/runs/39972953795): `SixPointFullDeltaArcDichotomy.lean` PASS, 9,110 targets. At `13*delta < n` the original six-centre `AngleCap` + uncompensated top deletion configuration admits EITHER two distinct non-gaining support-two minima OR one physical phase avoiding the ENTIRE canonical positive-gap delta arcs (not merely narrow bad intervals). Axioms exactly `[propext, Classical.choice, Quot.sound]`.

**Further bridging source committed, not yet verified at this checkpoint:**

* `PositiveToCriticalPhaseBridge.lean`: canonical quotient-one unit-gap slots embed into positive quotient gaps. Their starts require a real ring equality, not `rfl`, due to distinct real multiplication/division normalization forms. Fix committed, focused CI pending.
* `PositiveArcBoundaryCutBridge.lean`: transports one full-positive-arc-safe phase through the previous embedding to the `UncoveredBoundaryColoring` separating bit at a matching cut phase. Not yet kernel-verified.
* `PositiveArcSafeCutExistence.lean`: constructs the actual cut `c=x*pi/t` from a safe physical sample `x in [0,t)` and deduces separation of original boundary colour 0/n edges. Not yet kernel-verified.
* Dedicated focus workflows cover the dependencies and use pinned Lean/Mathlib, plus `jsp000404_sorry_audit.py` requiring at most one allowed root WIP `sorry`.

**Critical limitation:** the sole original `PlanarLowerBranchProofAdmittedWIP.lean` global non-reusing TRUE Boolean-hole/unreserved-surplus payment `sorry` remains. Neither stronger full-delta arcs nor boundary bipartite colouring imply dyadic capacity without an additional independently proved global accounting/charging theorem. No upstream complete-proof award claim is justified by this checkpoint.


## 2026-10-23 fifth continuation — direct positive-gap to critical-unit safety, kernel PASS

* [CI #39974094932](https://github.com/Charlie-Wang-03/awards/actions/runs/39974094932): `PositiveToCriticalPhaseBridge.lean` **PASS**, 9,111/9,111. Both `unitGapAsPositiveGap_start` and `full_positive_deltaArc_safe_implies_critical_unit_safe` have axioms exactly `[propext, Classical.choice, Quot.sound]`. The real normalization equality of physical starts needed `unfold ...; ring`, not a definitional `rfl`.
* Thus the **kernel-checked** local dependency is: (13 positive-gap slots, parameter (13δ<n) on the support-one/two branch) -> existence of a physical phase free of **every full positive-gap δ-arc** -> at that same phase every actual quotient-one cyclic critical interval is absent. This is stronger than the earlier direct positive-bad-subinterval escape.
* `PositiveArcBoundaryCutBridge.lean`, `PositiveArcSafeCutExistence.lean`, and `SixPointBoundaryCutDichotomy.lean` have been committed with separate CI gates. They attempt to transport the safe phase into a genuine cut `c=πx/t` carrying a coherent boundary Boolean 2-colouring. **Not kernel-verified at this checkpoint.** Any old failed downstream CI built before the normalized-start correction is stale.
* **Global original proof still open:** an actual non-reusing payment of true unhit Boolean holes and unreserved dyadic surplus against all genuine residual translated-loss, NET, rigid, soft, twin and collision debts, or an independently proved contradiction from failure of that payment. The original WIP `sorry` remains intentionally visible.


## 2026-10-23 sixth continuation — phase-to-real-boundary-cut, verified

**Newly kernel checked on the same research branch and pinned toolchain:**

* [Run #39975283387](https://github.com/Charlie-Wang-03/awards/actions/runs/39975283387): `PositiveArcBoundaryCutBridge.lean` PASS, no `sorryAx`. It transports full-positive-delta-arc phase safety to the genuine cut-boundary 0/n graph's Boolean edge separation, via all canonical q=1 critical slots.
* [Run #39978824071](https://github.com/Charlie-Wang-03/awards/actions/runs/39978824071): `PositiveArcSafeCutExistence.lean` PASS, 9,117/9,117 Lake targets. `exists_boundary_cut_coloring_of_full_positive_deltaArc_safe` constructs `c=x*pi/t in [0,pi)` from safe `x in [0,t)` and a real coherent `cutBoundaryWrapBit`. Printed axioms `[propext, Classical.choice, Quot.sound]`.
* [Run #39978965116](https://github.com/Charlie-Wang-03/awards/actions/runs/39978965116): `SixPointBoundaryCutDichotomy.lean` PASS, 9,118/9,118 Lake targets. `six_point_hard_top_two_support_two_or_boundary_bipartite_cut`: under actual six-point `AngleCap` geometry, top/minima exponent pattern, uncompensated top deletion and `13*delta<n`, either TWO DISTINCT actual non-gaining support-two minima remain, or an actual projective cut has a coherent Boolean bipartite 0/n boundary graph. Printed axioms `[propext, Classical.choice, Quot.sound]`.

**Additional proof engineering (under new focused CI when written):**
`PositiveArcSafeCutExistence`'s bound on `x*pi/t<pi` was repaired by reordering the commutative product. `ExactWitnessSupportThreeRemainder` and `SixPointExactWitnessPinnedExactGap` had `lam` bound AFTER its use in `AngleCap p lam`, accidentally introducing an independent implicit `lam✝`; this binder issue was fixed. The five-gap list proof was further repaired to remove impossible `g in []` from its last membership alternative. `SixPointAllDeltaBoundaryAlternative` eliminates the parameter threshold for n>=7 since delta<1/2 implies 13delta<7<=n. All three are only **candidate sources pending their own focused CI PASS**, not verified claims.

**No global prize proof:** the executable admitted `sorry` in
`PlanarLowerBranchProofAdmittedWIP.lean` remains. Boundary 0/n
bipartiteness does NOT alone provide the exact original-geometry,
globally non-reusing TRUE hole / unreserved surplus allocation against
all covered-loss, NET, twin, mixed-rigid, soft, and projected-loss
debts. It would be unsound to infer the latter from this local cut.
