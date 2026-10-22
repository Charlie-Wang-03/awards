# JSP-000404 — 2026-10-22 second-session Lean repairs and outlet dichotomy

Branch: `research/jsp-000404-sharp-centre`.
Status: research-only partial formalization. No complete proof or disproof is claimed.

## Verified improvements

### 1. Repair three previously failing Lean modules

Files:
- `JSP000404Research/ConcreteDoubleDeletionRestriction.lean`
- `JSP000404Research/SupportThreeNonTopGainPosition.lean`
- `JSP000404Research/SixPointUnitGapBudget.lean`

Focused GitHub Actions PASS:
https://github.com/Charlie-Wang-03/awards/actions/runs/39756458043

The proof changes:
- Restore the definitional equality for restricted child ray lists, explicitly instantiating the available `Nonempty` witness rather than leaving an implicit proof metavariable.
- Fix the `lam` parameter binder ordering in the actual support-three non-top wrapper; this avoids an auto-implicit `lam✝` mismatch.
- Supply an explicitly typed `Finset.single_le_sum` summand and rewrite the definitional exponent/floor-excess identity in two six-point unit-slot capacity bounds.

Build success: 3536 Lake jobs. `#print axioms` reports no `sorryAx` in the listed repaired theorem exports. In particular:
`six_point_top_five_minima_unitSupport_sum_le_ten` is now checked, yielding the genuine conditional six-centre one-top/five-minima unit quotient sum bound `<= 10`.

### 2. Actual six-point support-three middle-or-end outlet split (new lemma)

New file:
`JSP000404Research/SixPointSupportThreeOutletDichotomy.lean`.
Added to umbrella `JSP000404Research.lean` imports.

Theorem:
`JSP000404Research.six_point_support_three_middle_or_end_outlet`.

Focused CI PASS:
https://github.com/Charlie-Wang-03/awards/actions/runs/39755549221

Build: 3533 Lake jobs.
Kernel axiom audit:
`[propext, Classical.choice, Quot.sound]` (NO `sorryAx`).

For an *actual injective planar configuration* with genuine `AngleCap`, `n >= 4`, six original centres, a sharp top centre `s`, and a centre `i` having exponent `n-3` and quotient support three, the sharp-pinned cyclic list has
`qFirst :: qmid ++ [qLast]`, where the endpoints are positive and `qmid` has exactly three coordinates and exactly one positive coordinate `qHidden`.

Without assuming that `qHidden` is non-middle, the checked theorem exhibits the alternatives:
- exceptional middle shape `qmid = [0, qHidden, 0]`; or
- end shape `[qHidden, 0, 0]` or `[0, 0, qHidden]`, whose relevant non-top ray is flanked by positive quotients.

This is a sharper *proof interface*: earlier `SupportThreeNonTopGainPosition` requires a separate `hNoMiddle` premise. The new theorem makes that premise unnecessary for the case split, but it does not exclude the middle case or itself prove a compensated deletion.

### 3. Six-point support-two small-angle legacy repair

File: `JSP000404Research/SixPointSupportTwoSmallAngle.lean`.

Original incremental errors included nonexistent `List.getLastD_mem`, an incorrect nodup membership rewriting, an erroneous case-split equality term, a shadowed `lam` binder, and two reversed sharp endpoint inequalities.
The source was repaired and further refined after a focused failure exposed one remaining membership transport error.
The latest focused workflow is:
https://github.com/Charlie-Wang-03/awards/actions/runs/39756837018

**Verification at checkpoint authoring: PENDING.** Do not count this as PASS before the action's result and axiom audit are checked.

## Unclosed mathematics

- The original `PlanarLowerBranchProofAdmittedWIP.lean` deliberately retains exactly one executable `sorry`, at the unrestricted true six-source globally non-reusing payment gate. Its headline uses `sorryAx`. This source was *not* modified to bypass the mathematical obligation.
- The genuine `n=1`, `n=2` and at-most-four-original-centre branches are separate previously checked subcases.
- `n=3` with five original centres still has two exact overweight motifs: no exponent-two vertex with at least four exponent-one vertices, or one exponent-two and exactly one exponent-one vertex. Existing verified geometry supplies further necessary conditions but does not exclude either motif.
- The present new six-point dichotomy narrows a `n>=4` support-three terminal to the exceptional middle quotient pattern or an explicit non-top local outlet. A *global* non-reusing payment, or an actual geometric contradiction, is still required to close the lower branch.
- Focused proof-module PASS is not a whole-tree `lake build JSP000404Research` success. The latest previously completed fast-incremental full-target CI failed; the root entry remains unproved.

No new axioms, non-WIP `sorry` or unjustified solver credit were introduced. The source and verification evidence remain on the research branch only.
