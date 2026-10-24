# JSP-000404 — 2026-10-24 AngleCap geometric closure and Lean repair relay

**Scope:** research-only downstream work. This is NOT a complete proof or disproof of JSP-000404 / Erdős 504. The genuine global six-source non-reusing Boolean-hole/dyadic-surplus payment remains unproved, and the one executable `sorry` in `PlanarLowerBranchProofAdmittedWIP.lean` is intentionally retained.

## Kernel-verified new mathematical statements

1. `SeparatedSupportTwoResidualBudget.separated_support_two_double_zero_at_third_middle_mass_eq_zero`: for `delta = 1/3`, two zero top-adjacent quotient gaps force the intermediate original-plane zero-angle mass to equal zero. **Focused CI #40088902029 PASS**: 3554 Lake jobs, printed axioms [propext, Classical.choice, Quot.sound]. https://github.com/Charlie-Wang-03/awards/actions/runs/40088902029

2. `AngleCapNoncollinear.angleCap_not_collinear_of_distinct` and `angleCap_actual_angle_pos_of_distinct`: with `0 < lam`, actual `AngleCap` plus injective planar points forbids collinear triples and forces every distinct-triple actual Euclidean angle strictly positive. **Focused CI #40089492594 PASS**: 3203 Lake jobs, no `sorryAx`. https://github.com/Charlie-Wang-03/awards/actions/runs/40089492594

3. `ZeroAngleMassStrictPos.listZeroAngleMass_pos_of_zero_mem_and_angles_pos` and `all_consecutiveRayAngles_pos_of_AngleCap`: a genuine zero-quotient position has strictly positive actual-angle mass when paired actual angles are positive. **Focused CI #40090250957 PASS**: 3236 Lake jobs, no `sorryAx`. https://github.com/Charlie-Wang-03/awards/actions/runs/40090250957

4. `SeparatedSupportTwoThirdStrict.separated_support_two_six_centres_no_double_zero_at_third`: with precisely 6 original centres, `delta = 1/3`, sharp top exponent `n-1`, another centre exponent `n-3` and positive support 2, the two top-adjacent quotients cannot both be zero. The quotient cycle has five entries, so the three middle entries must contain a zero (only two total positives); strict original-angle positivity contradicts the proven zero-mass budget. **Focused CI #40091249457 PASS**: 3554 Lake jobs, printed axioms [propext, Classical.choice, Quot.sound], no `sorryAx`. https://github.com/Charlie-Wang-03/awards/actions/runs/40091249457

The original-plane theorems above are imported into `JSP000404Research.lean` at commit `110add8f5a5ad6ce04f5e568b4e683cda3015fc9`. This commit does not establish that the entire umbrella build is green.

## Focused engineering restoration

`FiveMinimaC4Extremal`, `CutSupportOneBadPalette`, `CutSupportTwoBadSmallAngle`, `CutSupportThreeBadSameBand`, and `ResidualSecondLayerTripleCanonical` are all restored at commit `7e7b1cdbcc029c83a123b6b5a9ed3ec33219bb7a` through an extracted shared `CyclicRealGapsNonneg` module, original cut-ray completeness, cardinality corrections and ordered list equalities.

**Focused CI #40091160636 PASS**: 9273 Lake jobs; no Lean compilation errors. Audited actual small-angle, five-minima C4, and QTT completion-owner statements print only ordinary Lean/Mathlib axioms, not `sorryAx`. https://github.com/Charlie-Wang-03/awards/actions/runs/40091160636

## New mathematical strengthening still needing separate verification

`SeparatedSupportTwoSixPlusStrict.lean` proposes a strict extension from exactly six to **at least six original centres** by replacing fixed five-ray enumeration with complete/nodup cycle cardinality and a `qmid.length >= 3` counting argument. It has no executable `sorry` or new axiom in the source. As of this checkpoint, the focused CI `JSP-000404 Focused Original AngleCap Noncollinear` for this generalization is **not yet reported as PASS**. Do not cite it as kernel-verified until inspecting that workflow run and its printed axioms.

## Exactly open mathematical frontier

`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` still has the only explicitly admitted `sorry` in `planar_lower_branch_dyadic_capacity_admitted_wip`. The true six-source global inequality requires an ACTUAL retained-active translated-loss choice with NON-REUSING allocation of all covered same-colour blockers, NET image duplicates, terminal twin and mixed-rigid obligations, soft overlap and projected losses, against TRUE holes outside translated-loss slices and genuinely unreserved dyadic surplus. Local original-plane short-angle certificates, support nonreuse, Hall/matching inequalities and the new delta=1/3 exclusion DO NOT supply that global payment by themselves.

**Do not** convert a covered sink, overlapping image, a synthetic/translated word or previously reserved surplus into a true unused hole. Do not add extra global assumptions, new axioms, `admit` or unreported proof holes.

## Verification and continuation

- Re-check focused six-plus CI before claiming the generalization.
- Audit the root umbrella `lake build JSP000404Research`, separately from focused builds; its WIP `sorryAx` remains expected and explicitly documented.
- Re-run `scripts/jsp000404_sorry_audit.py --root JSP000404Research --allowed-wip JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean --wip-max-sorries 1` and inspect `#print axioms` of new results.
- Prioritize genuinely unreserved global geometry/payment over additional cosmetic local counting lemmas.


## 2026-10-24 continuation — certified endpoint range and compilation repair

- **Five-module Lean repair is now kernel-verified**, not merely committed. Focused CI #40091160636 PASS, 9273 Lake jobs, no compilation errors: [run](https://github.com/Charlie-Wang-03/awards/actions/runs/40091160636). The modules are `FiveMinimaC4Extremal`, `CutSupportOneBadPalette`, `CutSupportTwoBadSmallAngle`, `CutSupportThreeBadSameBand`, and `ResidualSecondLayerTripleCanonical`.
- **Arbitrary finite >=6 original centres, delta=1/3:** `separated_support_two_at_least_six_centres_no_double_zero_at_third` kernel PASS, focused CI #40092391597 (3555 Lake jobs). Its `#print axioms` contains only `propext`, `Classical.choice`, and `Quot.sound`: [run](https://github.com/Charlie-Wang-03/awards/actions/runs/40092391597).
- **Entire interval 0 <= delta <= 1/3:** `separated_support_two_no_double_zero_of_delta_lt_third` for arbitrary finite centre sets and `separated_support_two_at_least_six_no_double_zero_of_delta_le_third` for >=6 actual centres are kernel PASS, focused CI #40092526954 (3556 Lake jobs), with the same ordinary axioms and no `sorryAx`: [run](https://github.com/Charlie-Wang-03/awards/actions/runs/40092526954).
- **Exact scope:** The obstruction requires a sharp top exponent n-1, a different centre exponent n-3 of positive support 2, n>=5, injective original-plane geometry, and actual AngleCap with lambda=pi/t. This excludes both top-adjacent quotient endpoints being zero in the specified range. It says nothing unconditional about all other hard carriers or the genuinely non-reusing global six-source payment.
- **Global frontier unchanged:** one intentionally admitted `sorry` inside `PlanarLowerBranchProofAdmittedWIP.lean`. No reduction in its executable `sorry` count is claimed and no extra axiom/false Boolean-hole credit is inserted.



## 2026-10-24 continued — actual projective gaps are strictly positive

- `AngleCapStrictProjectiveTheta.lean` proves `rayThetaAt_injective_of_AngleCap`, `centreProjectiveCycle_angles_nodup_of_AngleCap`, and `centreProjectiveCycle_gaps_pos_of_AngleCap`. Positive genuine `AngleCap` plus injective original planar points exclude coincident or antipodal projective rays; with sorted/nonduplicated angle lists and a strict wrap bound, **EVERY normalized cyclic projective gap is strictly positive**.
- Kernel: [Focused Strict Projective Theta CI #40093517326](https://github.com/Charlie-Wang-03/awards/actions/runs/40093517326) PASS, **3212 Lake jobs**, three printed axiom sets restricted to `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`.
- This is a reusable geometric strengthening of `CentreProjectiveCycle.gaps_nonneg`, not a proof that all Sendov gap quotients are positive. The floor of a strictly positive normalized gap may still be zero. Consequently **no Boolean true-hole resource, NET duplicate debt or unreserved surplus is newly paid** by this result.
- The one global `sorry` in `PlanarLowerBranchProofAdmittedWIP.lean` remains the sole executable admitted payment. No claim of a complete JSP-000404 proof/disproof.
