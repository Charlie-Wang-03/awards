# JSP-000404 — connector cut/C4 formalization relay (2026-10-24)

## Source and scope

- Research-only branch: `research/jsp-000404-connector-compiler-repair-20261024`.
- Source parent: `aed4dc326a320b43890d73f9705edd62ea2d0106` on `research/jsp-000404-sharp-centre`.
- The original JSP-000404 theorem is **not proved or disproved**.
- The single intentionally admitted global obligation remains `planar_lower_branch_dyadic_capacity_admitted_wip` in `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`. Its `sorry` must not be hidden by changing the theorem statement or adding axioms.

## Compilation-repair chain

Two exact historical failing modules were selected from the downstream cut/C4 workflow [40101434355](https://github.com/Charlie-Wang-03/awards/actions/runs/40101434355).

1. `CutSpanNMinusOneQuotientShape.lean`: convert active-cardinality saturated truncation into additive equality via `omega`, correct arguments to the saturated seam and local-band API, and derive the normalized terminal floor bound directly from genuine real-valued bounds.
2. `CutMonochromaticC4Angles.lean`: resolve the implicit wrap phase `delta`, instantiate the boundary-bit separation with explicit vertices, pass implicit angle-vertex parameters by name, and transport merged colours through the proved `localIncidentColor_mergeLastPartition` identity.

Intermediate workflow [40102725873](https://github.com/Charlie-Wang-03/awards/actions/runs/40102725873) reduced the source error set to three elaboration errors; [40103211284](https://github.com/Charlie-Wang-03/awards/actions/runs/40103211284) diagnosed further downstream API/floor/rewrite errors. Latest changes are subject to the focused check [40103871287](https://github.com/Charlie-Wang-03/awards/actions/runs/40103871287). **A commit or CI run in progress is not a PASS.**

## Five-minimum genuine C4 colour obstruction

The research-only `FiveMinimaC4UniqueCanary.lean` aims to establish:

- Any two *simple* 4-cycles on five vertices share an unordered edge.
- Hence two edge-disjoint local-colour graphs on five minima cannot both carry 4-cycles.
- Consequently the number of genuine monochromatic C4 exceptional colours on five minima is at most one (strengthening the existing at-most-two bound).

A purely combinatorial reason: the four-vertex supports of two cycles intersect in at least three vertices. On any shared triple, each cycle contains at least two of the three possible internal edges. Two two-element subsets of a three-element edge set intersect.

This is a finite graph lemma, *not* a geometric six-source payment. Its initial brute finite Lean proof hit a GitHub runner shutdown (exit 143), not a verified type failure or proof success. The finite case proof was changed to simplify degenerate first-cycle tuples before kernel decision; latest [focused verification](https://github.com/Charlie-Wang-03/awards/actions/runs/40103687396) remains an external proof gate.

## True missing global proof

The live `AngleCap` argument needs a non-reusing charge of real translated-loss and terminal twin/mixed/soft/covered-blocker debts into TRUE uncovered Boolean words outside all translated slices and *genuinely unreserved* dyadic slack. Existing local cycle/triangle/C4 and exact matching lemmas have not established that global allocation. In particular, a finite graph colouring lemma does not provide any new true-hole credit.

No custom axiom, new admitted proposition, first-complete-priority assertion, or upstream submission is intended by this branch.


## Continuation: verified mathematical reductions, 2026-10-24

GitHub branch is `research/jsp-000404-connector-compiler-repair-20261024`; draft PR is https://github.com/Charlie-Wang-03/awards/pull/6.

### Kernel-certified results (full SUCCESS, no `sorryAx` in named theorems)

| Workflow | Target | Status |
| --- | --- | --- |
| [40103687396](https://github.com/Charlie-Wang-03/awards/actions/runs/40103687396) | `FiveMinimaC4UniqueCanary` | SUCCESS: five minima, at most one C4-bearing edge-disjoint colour |
| [40107208313](https://github.com/Charlie-Wang-03/awards/actions/runs/40107208313) | `CutBadFourConsecutiveStepShape` | SUCCESS, 9,115 Lake jobs: each positive ordinary step quotient equals one under the span-three assumptions |
| [40107649425](https://github.com/Charlie-Wang-03/awards/actions/runs/40107649425) | `SixPointBadActiveC4`, `SixPointBadSharedC4Colour` | SUCCESS, 3,252 Lake jobs: both bad minima must activate the SAME C4-bearing colour under exact 3,3,2,2,2 reduced profile |
| [40107649419](https://github.com/Charlie-Wang-03/awards/actions/runs/40107649419) | `CutSpanNMinusOneQuotientShape`, `CutMonochromaticC4Angles`, `TwoBadMonochromaticC4Incidence` | SUCCESS, 9,135 Lake jobs: one of two bad minima on a forced cycle has an AngleCap-based strict sub-lambda angle |
| [40108090562](https://github.com/Charlie-Wang-03/awards/actions/runs/40108090562) | `SixPointBadSharedC4FromEquality` | SUCCESS, 3,253 Lake jobs: original six-point exact-equality assumptions imply a single C4 colour active at both bad minima |

In the absence of independent geometric constraints, the stronger claim
that BOTH bad minima lie ON the same four-cycle is false.
The explicit 3-colour K5 witness and its on-cycle/off-cycle active profile
are in `JSP000404_2026-10-24_ABSTRACT_C4_PROFILE_SATISFIABILITY.md`.

### Latest conditional conjunction

`SixPointCutSharedC4SmallAngle.lean` connects the exact six-point shared
colour and the genuine uncovered-cut two-bad small-angle theorems under
their common AngleCap assumptions. Its focused gate is
https://github.com/Charlie-Wang-03/awards/actions/runs/40108455064 .
Treat the result as **pending** until the gate returns success and
`#print axioms` excludes `sorryAx`.

### Unsolved original theorem

The admitted theorem
`ProjectionOrdered.planar_lower_branch_dyadic_capacity_admitted_wip`
still has exactly one intended executable `sorry`. The remaining
global proof obligation is the nonreused allocation of translated-loss
blockers, duplicate canonical images, terminal twin/mixed/soft and
other losses against **true external Boolean holes** and **unreserved**
dyadic surplus under actual AngleCap geometry. Conditional accounting
identities are not a payment proof, and covered words are not hole
credits. Do not assert JSP-000404 solved on the basis of this research PR.


## Second continuation: pendant vertex and two independent small-angle approaches

### Verified new kernel result

- [Five-minima pendant gate 40110980528](https://github.com/Charlie-Wang-03/awards/actions/runs/40110980528): **SUCCESS**, 3,251 Lake jobs; `degree_eq_one_of_active_off_fourCycle_no_cycle_through` has only `[propext, Classical.choice, Quot.sound]`. This fixes the formerly missing bipartite 2-colouring/no-triangle proof, explicit 12-term 4-cycle witness, and Mathlib finite-neighbour API. The theorem concludes: if an active fifth vertex lies on NO four-cycle in a bipartite five-vertex graph containing a C4, its degree is exactly one.

### Two subsequent routes — do not presume CI success

1. `FiveMinimaPendantRepeatedSmallAngle.lean` and `TwoBadEachSmallAngle.lean` form a *pendant-aware* proof that EACH bad minimum has an actual non-top small angle. The exact bottleneck was the pendant lemma, now certified. [CI 40110980490](https://github.com/Charlie-Wang-03/awards/actions/runs/40110980490), checked separately; investigate all remaining elaboration errors before claiming both-angle result.
2. `CutMergedTwoBadSmallAngles.lean` has a shorter *direct original-exponent* proof via four minimum-minimum incident edges and three non-root merged colours, followed by boundary merge injectivity and genuine same-cut-band small-angle geometry. Compiler error from reintroducing `lam` after `AngleCap p lam` was fixed in `71c8c76f`; [CI 40111014343](https://github.com/Charlie-Wang-03/awards/actions/runs/40111014343).
3. The new `SixPointCutBothBadSmallAnglesDirect.lean` bypasses the original-exponent and C4 pendant proof packages for a stronger exact-active-bounds-only result: root-factorize the cut partition, use the certified `four_nonTop_edges_three_nonroot_colours_repeat` at EACH bad vertex, then apply the certified `actual_angle_lt_lam_of_equal_uncovered_merged_color_at_saturation_bad`. [CI 40110888692](https://github.com/Charlie-Wang-03/awards/actions/runs/40110888692). It is submitted, **not yet certified** at this checkpoint.

### Global proof boundary

The full theorem still needs ONE global six-source payment with a nonreusing injection into **actual true outside-translated Boolean holes** plus genuinely unreserved dyadic surplus. Small-angle witnesses are local geometry and alone provide neither that injection nor adequate surplus. New local modules must not be imported as a fake global proof.


## PROVEN shorter route: EACH bad minimum gets an actual small angle

**SUCCESS:** [40110888692](https://github.com/Charlie-Wang-03/awards/actions/runs/40110888692), 9,121 Lake jobs. The new stronger local theorem
`six_point_cut_both_bad_minima_have_strict_small_angles_direct` printed **only**
`[propext, Classical.choice, Quot.sound]`, not `sorryAx`.

Its exact input is the SAME six-point un-covered cut-merged active-card
bounds (`top ≤1, bad₁ ≤4, bad₂ ≤4, all other minima ≤3`),
both `CutSaturationBadAt`, and genuine `AngleCap` geometry.
Its conclusion provides a strict sub-`lam` non-top two-ray angle
**separately at EACH of the two bad minima**.

The proof is significantly shorter than the pendant-C4 alternative:
`six_point_two_exception_root_factorization`
→ `four_nonTop_edges_three_nonroot_colours_repeat` *twice*
→ `actual_angle_lt_lam_of_equal_uncovered_merged_color_at_saturation_bad` *twice*.
This requires NO monochromatic C4 and NO assumption that both bad minima
lie on a selected C4. The independent C4 uniqueness and pendant results
remain useful for different structural cases but are now *unnecessary*
for the two-angle consequence.

**Also SUCCESS:** [40111014343](https://github.com/Charlie-Wang-03/awards/actions/runs/40111014343), 9,116 Lake jobs: the existing
`uncovered_cut_two_bad_minima_have_small_nonTop_angles` original-exponent
terminal theorem, after correcting duplicated `lam` in its binder
sequence. Its axiom list is `[propext, Classical.choice, Quot.sound]`.

A stronger conjunction
`six_point_cut_shared_C4_and_both_bad_small_angles` is submitted in
`SixPointCutSharedC4BothBadAngles.lean`; follow its separate
[40111507155](https://github.com/Charlie-Wang-03/awards/actions/runs/40111507155)
kernel gate before making acceptance claims. The optional
pendant-aware proof file `TwoBadEachSmallAngle.lean` has a separate
[40111643182](https://github.com/Charlie-Wang-03/awards/actions/runs/40111643182)
gate. Those paths are NOT required by the verified direct two-angle theorem.

**Unsolved:** the all-cardinality original theorem still retains ONE genuine
`sorry` for the global nonreusing six-source payment into REAL external
Boolean holes plus genuinely unreserved dyadic surplus. A small angle at
two centres cannot be treated as a newly discovered hole or as spare mass.


## Next verification checkpoint — exact six-point terminal and compiler audit

### Certified after the previous handoff

- [CI 40111507155](https://github.com/Charlie-Wang-03/awards/actions/runs/40111507155): **SUCCESS**, 9,126 Lake jobs. `six_point_cut_shared_C4_and_both_bad_small_angles` has axioms exactly `[propext, Classical.choice, Quot.sound]`, **no sorryAx**. Same true uncovered-cut profile gives *simultaneously* a C4-bearing colour active at each bad minimum and an actual non-top strict sub-lambda angle at each.
- [CI 40110888692](https://github.com/Charlie-Wang-03/awards/actions/runs/40110888692): **SUCCESS**, 9,121 Lake jobs, direct both-angle theorem; the optional C4/pendant case split is NOT needed to establish this consequence.
- [CI 40111014343](https://github.com/Charlie-Wang-03/awards/actions/runs/40111014343): **SUCCESS**, 9,116 Lake jobs, original-exponent cut two-bad direct small-angle theorem.
- [CI 40110980528](https://github.com/Charlie-Wang-03/awards/actions/runs/40110980528): **SUCCESS**, 3,251 jobs; genuine bipartite 5-minimum off-cycle pendant theorem with no sorryAx.

### New code submitted on this continuation

- `TwoBadEachSmallAngle.lean`: replaced a time-consuming C4/pendant case split with a direct proof, while PRESERVING theorem signatures, using the certified 4-to-3 repeated-colour pigeonhole and the actual-cut angle lemma. [CI 40112323821](https://github.com/Charlie-Wang-03/awards/actions/runs/40112323821), gate verdict pending at write time.
- `FiveMinimaPendantRepeatedSmallAngle.lean`: remains useful as the stronger *non-C4-colour* repeated-edge witness when the bad vertex is pendant off the selected C4. Its declaration and C4 orientation/API repairs are on branch. Independent [CI 40112349807](https://github.com/Charlie-Wang-03/awards/actions/runs/40112349807) checks this stronger structural file, gate pending at write time.
- `SixPointCutTwoBadCompleteLocalCertificate.lean`: combines exact original n-1 / n-3 exponents, AngleCap and two bad minima into a SINGLE external-auxiliary-free local certificate: sharp top, shared non-root C4-bearing colour, two separately non-top strict small angles, and two different phase-synchronous canonical bad turn-unit slots. Calls three prior research theorems with their EXACT geometric hypotheses. Dedicated [CI 40112599605](https://github.com/Charlie-Wang-03/awards/actions/runs/40112599605), gate pending.
- `.github/workflows/jsp000404-full-admitted-root-audit.yml`: new explicit whole-root compiler gate [CI 40112204828](https://github.com/Charlie-Wang-03/awards/actions/runs/40112204828), building `JSP000404Research.PlanarLowerBranchProofAdmittedWIP` after the executable-sorry audit. This root file INTENTIONALLY has one global `sorry`. Even a fully green compilation does NOT turn the original problem into a proof.

### Exact unresolved obligation

At the end of `PlanarLowerBranchProofAdmittedWIP.lean` (near line 900), one executable admitted proof remains: for general original numbers of centres with n≥3 beyond the proved special configurations, show an ACTUAL planar nonreusing allocation of the global loss, already-covered soft/hard blocker, duplicate NET target, twin, mixed-rigid and other debts against **TRUE Boolean holes outside translated-loss credit** plus genuinely **unreserved** dyadic profile surplus. A C4-colour or small-angle witness is not itself a Boolean hole, a spare dyadic term or an admissible resource double-charge. No new axioms, no new admitted lemma, no full-prize-proof claim.


## Root compilation and strengthened pendant subbranch — CONFIRMED CI

- **[40112204828](https://github.com/Charlie-Wang-03/awards/actions/runs/40112204828) SUCCESS**, 3,826 Lake jobs: built `JSP000404Research.PlanarLowerBranchProofAdmittedWIP` and broad genuine dependencies. Executable-proof audit explicitly prints `PlanarLowerBranchProofAdmittedWIP.lean:900: explicit sorry`, `WARNING: the WIP root theorem depends on Lean sorryAx`, and `PASS: zero executable sorry/admit outside the exact allowed WIP path`. This is FULL ROOT COMPILATION only, not a valid proof or disproof of JSP-000404.
- **[40112349807](https://github.com/Charlie-Wang-03/awards/actions/runs/40112349807) SUCCESS**, 9,123 Lake jobs: both `pendant_bad_has_repeated_nonC4_colour` and `pendant_saturation_bad_has_repeated_small_angle` now have precisely `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. The repeated pair at an off-C4 pendant bad minimum is in a different colour from the C4-bearing colour and yields a true strict sub-lambda angle.
- Refactored `TwoBadEachSmallAngle.lean` to use only the certified direct 4-to-3 pigeonhole route. The first refactor CI failed from a malformed text splice at `let M`; that splice and the lost documentation-comment start were repaired by commit `5b714607`. Its [latest CI 40112876834](https://github.com/Charlie-Wang-03/awards/actions/runs/40112876834) must be inspected, not presumed green.
- The [full six-centre cut local certificate CI 40112599605](https://github.com/Charlie-Wang-03/awards/actions/runs/40112599605) remains pending at this checkpoint.

**One admitted true-hole/surplus global capacity obligation is still open.** The above establishes a compiler-clean original root (with an explicit, recognised `sorry`), and two more useful local geometric constraints. The compiled root is NOT a proof.


## Final continuation gate verdicts — all four latest targets SUCCESS

This overrides older "pending" statements above for the same runs:

| Run | Module | Result |
| --- | --- | --- |
| [40112204828](https://github.com/Charlie-Wang-03/awards/actions/runs/40112204828) | `PlanarLowerBranchProofAdmittedWIP` full root | **SUCCESS** 3,826 jobs; audit exactly ONE explicit `sorry` at line 900 and zero elsewhere; root **still has sorryAx** |
| [40112349807](https://github.com/Charlie-Wang-03/awards/actions/runs/40112349807) | `FiveMinimaPendantRepeatedSmallAngle` | **SUCCESS** 9,123 jobs, two nonC4-colour/true-angle statements **no sorryAx** |
| [40112599605](https://github.com/Charlie-Wang-03/awards/actions/runs/40112599605) | `SixPointCutTwoBadCompleteLocalCertificate` | **SUCCESS** 9,123 jobs; sharp top + SAME non-root C4 colour + TWO DISTINCT simultaneous bad turn slots + TWO true small angles, **no sorryAx** |
| [40112876834](https://github.com/Charlie-Wang-03/awards/actions/runs/40112876834) | `TwoBadEachSmallAngle` refactor | **SUCCESS** 9,122 jobs; both named theorems (`exceptional_bad_has_nonTop_small_angle`, `two_exception_bad_minima_each_have_small_angle`) have standard axioms only, **no sorryAx** |

For the latter three runs, exactly `[propext, Classical.choice, Quot.sound]` was printed in `#print axioms`. The prior proven [40111507155](https://github.com/Charlie-Wang-03/awards/actions/runs/40111507155) independently proves shared C4 plus two bad angles under active-card bounds.

**REMAINING mathematical bottleneck**: original global all-cardinality nonreusing six-source accounting into TRUE external Boolean holes and NET unreserved dyadic surplus. The sole admitted main theorem is not a complete proof, and no full-disproof is established. Do not conflate a SUCCESS root build with proof closure.


## 2026-10-25 — Global true-hole nonreuse reformulation / Lean handoff

This continuation targets the EXACT remaining source-based frontier
from `PlanarLowerBranchProofAdmittedWIP.lean:~476–900`:

```
terminalTwinOtherFiveDebt(B,k)
+ card(actual retained-edge covered blocker union)
+ translatedLossDuplicateDebt(B,k,choice)
≤ card(TRUE holes outside all translated-loss slices)
+ terminalTwinAvailableSurplus(B,k)
```

The main theorem has exactly ONE admitted proof and remains open.

### Genuine new kernel-verified facts

- [CI 40114532776](https://github.com/Charlie-Wang-03/awards/actions/runs/40114532776) **SUCCESS**, 3,419 Lake jobs, ordinary axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`: `ActualExternalHoleNonreuseCertificate.lean` constructs an **explicit source-tagged debt / genuine-credit type**, and proves a single *injective* matching into exterior TRUE holes or the pre-deducted surplus is sufficient for the exact outstanding numeric inequality.
- [CI 40114532801](https://github.com/Charlie-Wang-03/awards/actions/runs/40114532801) **SUCCESS**, 3,420 Lake jobs, standard 3 axioms, no `sorryAx`: `ActualExternalHoleSeparatedSourcePayment.lean` proves that separate source maps pay the total only if the individual maps are injective AND all three pairs of image classes are disjoint. This rules out cross-source double spending.
- [CI 40114739960](https://github.com/Charlie-Wang-03/awards/actions/runs/40114739960) **SUCCESS**, 3,318 Lake jobs, standard 3 axioms, no `sorryAx`: `ActualExternalHoleCoveredBlockerSeparation.lean` establishes ACTUAL covered blocker union is SUBSET of coveredCompletionWords and strictly DISJOINT from outside-translated TRUE Boolean holes. An already covered blocker word is categorically NOT itself a valid hole payment.

### Deeper nonreuse interfaces, pending final kernel verdicts

- `ActualEightSourceNonreuseCertificate.lean`: the SIX terminal categories remain individually source-tagged (actual soft words, forward/reverse hard words, twin dyadic mass, ascending mixed, descending mixed), as do actual covered blocker WORDS and duplicate mass: EIGHT debt classes to TWO genuine resources. [CI 40114872463](https://github.com/Charlie-Wang-03/awards/actions/runs/40114872463).
- `PlanarCapacityOfGlobalTrueHoleNonreuseInjection.lean`: conditional sufficient bridge from the three-tag injection to the ENTIRE original planar dyadic-capacity conclusion. [CI 40115000977](https://github.com/Charlie-Wang-03/awards/actions/runs/40115000977). Corrected Lean namespace `open DirectionData` after initial failure.
- `PlanarCapacityOfEightSourceNonreuseMatching.lean`: same all-cardinality planar capacity bridge from the fully tagged eight-class injection. [CI 40115006117](https://github.com/Charlie-Wang-03/awards/actions/runs/40115006117).
- `ActualEightSourceHallPaymentCriterion.lean`: finite Hall's marriage theorem converts actual-source eligible-credit NEIGHBOURHOOD EXPANSION of every subset of the eight-class debt domain to one global nonreusing allocation. [CI 40115194428](https://github.com/Charlie-Wang-03/awards/actions/runs/40115194428). The formal Hall conclusion is CONDITIONAL, not a geometric proof that expansion holds.

### Essential mathematical boundary

These theorems clarify the REAL remaining geometry and rule out several bookkeeping shortcuts. Their antecedent injection / eligible Hall expansion is NOT proved from AngleCap. A purely numerical injection between abstract cardinalities is a certificate interface, NOT the missing geometrically forced construction. The named Boolean-hole credit subtype is defined as original globally uncovered words MINUS ALL translated-loss slices; the surplus credit index has the existing exact already-pre-reserved deduction. In particular NO covered soft word, blocker word or canonical NET shadow can be silently promoted to a TRUE hole.

No axiom, new `sorry`, changed theorem assumption, accepted prize proof, or upstream submission. Maintain Draft PR #6.


### Updated kernel verdicts for nonreuse/Hall interfaces

These completed statuses supersede "pending" above:

- [40114872463](https://github.com/Charlie-Wang-03/awards/actions/runs/40114872463) **SUCCESS**, 3,420 jobs; `actual_eight_source_injective_payment_suffices` formally preserves all SIX terminal source categories plus actual covered-loss blocker words and duplicate debt, with only two legal external-resource categories; axioms exactly the three standard Mathlib axioms, **no sorryAx**.
- [40115000977](https://github.com/Charlie-Wang-03/awards/actions/runs/40115000977) **SUCCESS**, 3,420 jobs; `planar_lower_branch_capacity_of_global_true_hole_nonreuse_injection` connects the tagged actual payment certificate to the ORIGINAL all-cardinality planar dyadic-capacity conclusion, conditional on the missing ACTUAL matching; **no sorryAx**.
- [40115194428](https://github.com/Charlie-Wang-03/awards/actions/runs/40115194428) **SUCCESS**, 3,428 jobs; `actual_eight_source_hall_condition_implies_payment` uses pinned Mathlib Hall theorem to certify that EVERY-subset neighbourhood expansion of debt units into eligible REAL credits produces the needed globally injective payment; **no sorryAx**.

Latest conditional planar variants have a fixed `#print axioms` template bug; successful Lean verdict must be checked separately:
[40115544989](https://github.com/Charlie-Wang-03/awards/actions/runs/40115544989) (8-class matching → full planar), [40115551185](https://github.com/Charlie-Wang-03/awards/actions/runs/40115551185) (8-class Hall expansion → full planar).

**Not solved:** no theorem proves the chosen geometric eligibility neighbourhoods satisfy Hall expansion under AngleCap. In particular an arbitrary full neighbourhood would merely restate the outstanding numerical inequality. The one original global `sorry` remains at `PlanarLowerBranchProofAdmittedWIP.lean:900`.


## 2026-10-25 — ACTUAL loss-collision square: candidate external-hole exclusion

**Last pending prior gates CONFIRMED:**
- [CI 40115544989](https://github.com/Charlie-Wang-03/awards/actions/runs/40115544989): **SUCCESS**, 3421 Lake jobs; `planar_lower_branch_capacity_of_eight_source_actual_nonreuse_matching`, only ordinary `[propext, Classical.choice, Quot.sound]` axioms.
- [CI 40115551185](https://github.com/Charlie-Wang-03/awards/actions/runs/40115551185): **SUCCESS**, 3429 Lake jobs; `planar_lower_branch_capacity_of_eight_source_Hall_expansion`, ordinary axioms only. **BOTH ARE STILL CONDITIONAL:** actual planar Hall expansion / allocation existence not established.

**New direct, mathematically unconditional collision-credit exclusion:**
- `ResidualLossCollisionThreePointExternalHoleObstruction.lean` reuses REAL original loss-collision predecessor theorems. Every shared word `w` of two *distinct* actual translated-loss coordinate slices `c,d` gives THREE pairwise DISTINCT forbidden external TRUE-hole credits:
  - `w` is inside translated-loss set and thus OUTSIDE-hole-ineligible;
  - `flip(w,c)` is an ACTUALLY covered original completion word;
  - `flip(w,d)` is a distinct ACTUALLY covered original completion word.
- [CI 40117561435](https://github.com/Charlie-Wang-03/awards/actions/runs/40117561435): **SUCCESS**, 3320 Lake jobs. The three elementary/real-collision exclusion theorems have no `sorryAx`.
- The same file has the follow-up TWO-FLIP FOUR-CORNER SQUARE theorem: only the *opposite double-flip* corner `flip(flip(w,c),d)` can POSSIBLY be a TRUE exterior hole; the actual exterior-hole cardinality of the whole four-corner square is at most ONE. **This does not assert that fourth corner actually IS an exterior hole.** Independent [CI 40117821203](https://github.com/Charlie-Wang-03/awards/actions/runs/40117821203) must complete before marking the square statement kernel-certified.
- The double-flip may be covered by an external (third) centre or lie in another translated-loss slice; one must explicitly prove genuine uncoveredness and global distinct allocations for any proposed refund. A local square/three-point obstruction is NOT an entire all-centre six-source payment.
- We added the dedicated new current-HEAD workflow `.github/workflows/jsp000404-focused-actual-collision-square.yml` to ensure the amended square/cardinality statements get a fresh kernel gate.

**Still exactly one research-root executable `sorry`** in `PlanarLowerBranchProofAdmittedWIP.lean:900`; no new admit, no upstream prize proof/disproof, PR stays Draft.


## 2026-10-25 — Exact ORIGINAL collision-square hole iff and positive duplicate branch

These updates **supersede** prior pending descriptions of the square CI:

1. **[40118219163](https://github.com/Charlie-Wang-03/awards/actions/runs/40118219163) SUCCESS, 3320 Lake jobs**: both
   `cross_loss_collision_square_external_hole_only_double_flip` and
   `cross_loss_collision_square_external_holes_card_le_one` have standard axioms only, **NO sorryAx**. The double-flip corner is the SOLE possible exterior true-hole inside an actual collision's four-corner Boolean square; there may be ZERO exterior holes. One compiler failure in the first run was a missing right parenthesis in nested Finset.insert cardinality syntax, fixed by commit `d25c7f03`.
2. **[40118501850](https://github.com/Charlie-Wang-03/awards/actions/runs/40118501850) SUCCESS, 3322 Lake jobs**: `actual_loss_collision_double_flip_true_hole_forces_cross_activity` and its exterior variant are BOTH kernel-checked, **NO sorryAx**. If the only plausible local refund corner `flip(flip(w,c),d)` is actually a TRUE hole, the first source's ORIGINAL retained-active set MUST contain d and the second source's must contain c. Proof: otherwise inactive-coordinate completion closes the alleged hole with one of its OWN two original source cubes.
3. **[40118646836](https://github.com/Charlie-Wang-03/awards/actions/runs/40118646836) SUCCESS, 3323 Lake jobs**: `actual_loss_collision_double_flip_external_hole_iff` is an exact source-native IFF, **NO sorryAx**. The only local candidate q is genuinely outside-translated TRUE hole iff:
   - d active at c-owner v,
   - c active at d-owner u,
   - q lies in NO third-party original completion cube,
   - q lies in NO translated-loss slice.
   Proof uses actual distinct original collision owners, inactive-flip cube invariance, active-flip cube exit, and the exact Boolean complement definition. **It does NOT assert these four conditions always hold.**
4. `ResidualLossDuplicateDebtSquareDichotomy.lean` is a new global numerical/source bridge: when the literal `translatedLossDuplicateDebt>0`, a REAL coordinate collision and a four-corner square with at most one hole must exist; otherwise debt is zero. **[40118791070](https://github.com/Charlie-Wang-03/awards/actions/runs/40118791070) was pending** at this checkpoint; verify before elevating.
5. `ResidualLossCommonActiveColourNoDuplicate.lean` is a constructive opposite branch: if the actual projected-loss sources SHARE ONE genuinely retained-active colour c0, choosing c0 at every loss vertex yields exactly zero cross-coordinate duplicate debt, with NO hole/surplus credit assumed. **[40119012594](https://github.com/Charlie-Wang-03/awards/actions/runs/40119012594) was pending** at this checkpoint; verify before elevating.

The global one-sorry six-source actual external-Boolean-hole PLUS net available-surplus injection is **NOT** proved. The exact local criterion and the common-colour zero-duplicate branch reduce particular source-native subproblems without establishing that the required source conditions hold in all AngleCap configurations, nor that candidate holes across collisions can be used injectively.


## 2026-10-25 further source-native proof chain — updated results

- [40118219163](https://github.com/Charlie-Wang-03/awards/actions/runs/40118219163) **PASS, 3320 jobs**; real cross-coordinate collision four-corner square has at most one possible exterior true hole, the OPPOSITE double-flip corner; no sorryAx.
- [40118501850](https://github.com/Charlie-Wang-03/awards/actions/runs/40118501850) **PASS, 3322 jobs**; the double-flip corner being a true hole NECESSARILY requires BOTH original source owners to be retained-active on the OTHER endpoint's chosen coordinate. Uses actual original retained-cube invariance (inactive flips cannot create holes); no sorryAx.
- [40118646836](https://github.com/Charlie-Wang-03/awards/actions/runs/40118646836) **PASS, 3323 jobs**; exact source-native IFF for double-flip exterior true-hole eligibility: (1) both cross-activities, (2) no third-party original retained cube covers the target, (3) the target lies outside EVERY translated-loss slice. No sorryAx. This is a real geometric TRUE-hole test, not its universal existence.
- [40118791070](https://github.com/Charlie-Wang-03/awards/actions/runs/40118791070) **PASS, 3321 jobs**; positive ORIGINAL `translatedLossDuplicateDebt` ALWAYS forces at least one genuine cross-coordinate collision square with at most one exterior hole. Its converse branch is exact duplicate debt ZERO. No sorryAx.
- `ResidualLossCommonActiveColourNoDuplicate.lean` constructs an actual constant active loss-coordinate choice eliminating ALL duplicate debt, IF one retained-active colour is shared by ALL projected-loss sources. Initial CI [40119012594](https://github.com/Charlie-Wang-03/awards/actions/runs/40119012594) failed a **parenthesis** typo in `Finset.univ : Set` coercion, fixed in `e54630a9`; fresh [40119405552](https://github.com/Charlie-Wang-03/awards/actions/runs/40119405552) pending.
- `ResidualLossAtMostOneSourceZeroDuplicate.lean` derives a full active zero-duplicate choice with NO additional source-colour assumption whenever original projected-loss source count ≤1, using the already certified positive retainedActive palette. [CI 40119405532](https://github.com/Charlie-Wang-03/awards/actions/runs/40119405532) pending.

**Scope warning:** a choice making duplicate debt zero can CHANGE the ACTUAL covered translated blockers and exterior-hole count. Therefore duplicate-zero alone is not a valid global six-source payment; it is a genuine elimination of only ONE ledger term, with other terms still to be paid. The main single admitted `sorry` at `PlanarLowerBranchProofAdmittedWIP.lean:900` remains untouched. No theorem claim beyond proven CI evidence.


## 2026-10-25 continued — verified collision-square TRUE-hole scarcity

This checkpoint separates TWO distinct outcomes: (i) genuinely proven
original-Boolean-cube resource EXCLUSIONS; (ii) genuinely proven
sufficient choices eliminating projected-loss duplicate debt.
Neither outcome by itself proves all-cardinality six-source payment.

### New unconditional kernel-approved collision obstructions

| GitHub Actions | New theorem scope | Verifiable result |
| --- | --- | --- |
| [40117561435](https://github.com/Charlie-Wang-03/awards/actions/runs/40117561435) | `cross_loss_collision_three_distinct_non_external_holes` | SUCCESS 3,320 jobs, `w` lies in translated loss while both distinct immediate flips are ORIGINAL covered, so all THREE exclude real outside-translated true-hole credit |
| [40119237706](https://github.com/Charlie-Wang-03/awards/actions/runs/40119237706) | `cross_loss_collision_square_external_hole_only_double_flip`, `cross_loss_collision_square_external_holes_card_le_one` | SUCCESS 3,320 jobs: only opposite double-flip can be credited, at most 1 real exterior hole on the square |
| [40119237695](https://github.com/Charlie-Wang-03/awards/actions/runs/40119237695) | `positive_loss_duplicate_debt_forces_one_hole_square` | SUCCESS 3,321 jobs: every positive ORIGINAL exact translated-loss duplicate debt yields an actual collision square subject to this ≤1 capacity |
| [40119335142](https://github.com/Charlie-Wang-03/awards/actions/runs/40119335142) | `actual_loss_collision_inactive_cross_square_no_external_holes` | SUCCESS 3,324 jobs: if either original source owner lacks the OTHER loss coordinate in retainedActive, then the ENTIRE local collision square has ZERO genuine exterior holes |
| [40119536010](https://github.com/Charlie-Wang-03/awards/actions/runs/40119536010) | `cross_loss_collision_square_exterior_holes_exact_singleton` and `_exact_count` | SUCCESS 3,321 jobs: literally `square ∩ real exterior holes = {opposite two-flip word} ∩ real exterior holes`; exact local cardinality is 0 or 1 based on actual membership |

All those named Lean lemmas' `#print axioms` exclude `sorryAx`.

### Two complementary routes that really make duplicate debt ZERO

- [40119750833](https://github.com/Charlie-Wang-03/awards/actions/runs/40119750833) SUCCESS, 3,308 jobs: `common_retained_active_colour_gives_zero_loss_duplicate_choice`. If all actual projected-loss vertices have ONE shared actual retained-active coordinate, pick it as the common flip choice; the exact ORIGINAL global cross-coordinate duplicate debt is 0. Fixed Lean elaboration from `Function.onFun Disjoint` to concrete finite-set `Disjoint` before `Finset.disjoint_left`.
- [40119750866](https://github.com/Charlie-Wang-03/awards/actions/runs/40119750866) SUCCESS, 3,312 jobs: `at_most_one_projected_loss_vertex_has_active_zero_duplicate_choice`. At most one actual projected-loss source eliminates the exact duplicate debt with a legitimate active choice.

### Pending exact geometric one-hole criterion

`ResidualLossCollisionExactLocalHoleEligibility.lean` combines the
new exact square 0/1 count and the earlier source-native double-flip
IFF criterion. It asserts that a square contributes exactly ONE
eligible real exterior hole IFF both source-cross activities hold,
all third-party original retained cubes exclude the opposite word,
and all translated-loss slices exclude the opposite word.
[CI 40119968385](https://github.com/Charlie-Wang-03/awards/actions/runs/40119968385)
was still in progress at the time of this relay entry. It is NOT
kernel-certified until SUCCESS.

### Remaining explicit mathematical gap

A positive global duplicate debt is NOT a license to refund a TRUE hole:
the actual local square may have 0 holes. Even if it has 1, MULTIPLE
collision events can point to the SAME opposite double-flip word.
A valid proof must establish a globally NONREUSING matching (or an
equivalent direct capacity inequality) for ALL eight original debt
source classes under actual planar `AngleCap`; no such existence
theorem is yet known. The sole global `sorry` at
`PlanarLowerBranchProofAdmittedWIP.lean:900` remains untouched.
No merge, additional axiom, new sorry, or solved/disproved claim.
