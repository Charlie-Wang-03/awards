# JSP-000404 — Lean root-chain repair and exact eleven-centre NET ledger

**Date:** 2026-10-14
**Research branch:** `research/jsp-000404-sharp-centre`
**Latest Lean source HEAD under root-chain audit:** `9bc28244a34ebdc95fe2a78696f9dd7e5dd190f3`
**Status:** PARTIAL. The restricted double-hit lemmas are kernel-checked; the umbrella root import is NOT green, and the full JSP-000404 mathematics is still open.

## The verified mathematics

The imported source-native hard-carrier theorem gives
`4 * |F_d| <= |V|` for every ACTUAL NET diagonal fibre `F_d`.
When `Fintype.card V <= 11`, every `F_d` has cardinality at most two.
Since every `d` in the actual image has at least one source, exact
duplicate debt satisfies

    E_D = sum_(d in actual image) (|F_d| - 1)
        = #{d in actual image : |F_d| = 2}
        <= |actual image|.

These are actual collision targets, NOT necessarily free Boolean holes.
They do not remove covered-target, terminal-twin, mixed-rigid, soft overlap
or fifth-centre geometrical payment obligations.

**Verified module:**
`JSP000404Research/ResidualNetCollisionElevenCentreDoubleHit.lean`.
Three declarations:

- `net_collision_fibre_card_le_two_of_centres_le_eleven`
- `net_collision_duplicate_debt_eq_double_hit_card_of_centres_le_eleven`
- `net_collision_duplicate_debt_le_diagonal_image_card_of_centres_le_eleven`

Independent incremental Lean CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38548784678

Result: SUCCESS, 3465 build jobs. All three theorems print
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

The proof also imports in
`PlanarLowerBranchProofAdmittedWIP.lean`. The original admitted
global six-source payment is **unchanged** and must not be counted as
closed.

## Root-chain compilation repair

A deliberate import into `JSP000404Research.lean` exposed numerous
pre-existing/stale root-dependency elaboration failures previously hidden
by focused incremental builds.

Repair work was performed on legacy modules involving:

- outdated `Mathlib.Data.Matrix.Notation` import;
- missing `OrderedBandCode` import;
- `Finset.univ.erase` DecidableEq arguments and deletion double-counting;
- wrong `finTwoEquiv` orientation;
- dependent `DirectionData` width rewrites;
- `IsLow` / `IsHigh` definitional simplification in symmetric wrap predicates;
- unequal multiplication factor order in real inequalities;
- a wrong application of the `support_budget_fails_iff_floorExcess_lt`
  equivalence WITHOUT its required quotient-total hypothesis. This was
  replaced by an independent direct truncated-subtraction lemma in
  `BoundaryFailureStructure.lean`, without adding a mathematical premise.

These changes compile in parts of later full-root attempts; **do not
infer full-root success from the preceding text**.

**Latest full-root incremental audit:**
https://github.com/Charlie-Wang-03/awards/actions/runs/38551868255
on source commit `9bc28244a34ebdc95fe2a78696f9dd7e5dd190f3`

Conclusion: FAILURE. Remaining reported broken modules:

1. `RestrictedDeletion.lean`: missing decidable equality and argument mismatch.
2. `StableCounterexampleData.lean`: finite sum identity `change` elaboration.
3. `WrapSwitch.lean`: typeclass and parity/symmetric wrap argument mismatches.
4. `BoundaryExcessBalance.lean`: partial-function projection / missing hypothesis.

Some declarations in failing modules show `sorryAx` **as a side effect of
failed compilation**. They are NOT validated and MUST NOT be represented
as complete theorems. There is still one deliberate `sorry` in the
separate `PlanarLowerBranchProofAdmittedWIP.lean`.

## Mathematical remaining obligation

The unrestricted theorem requires a GLOBAL geometry-correct, non-reused
payment/capacity inequality across actual NET collision sources. In
particular, proving upper bounds on single fibre multiplicities does
not establish the global payment among covered diagonals, true holes,
terminal twins and mixed carriers. The <=11-centre lemma is a genuinely
proven local reduction, NOT a complete JSP-000404 proof/disproof.

## Verification policy

Do not merge this research branch as a full theorem submission.
Do not introduce new `sorry`, new axioms, fabricated CI status,
or count syntax fixes as mathematical closure.
On subsequent repair, check new head-specific CI logs AND all axioms,
then keep global proof work independent from legacy root import cleanup.
