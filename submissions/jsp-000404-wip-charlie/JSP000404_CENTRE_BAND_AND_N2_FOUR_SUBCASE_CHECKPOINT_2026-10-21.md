# JSP-000404 | 2026-10-21 research checkpoint

**Status:** ongoing, not a full proof or disproof. Branch: `research/jsp-000404-sharp-centre`.
One intentionally admitted global `sorry` still exists in
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`.
The original proof gate is non-reusing actual six-source payment:
real outside TRUE Boolean holes and genuinely unreserved surplus must pay
all soft, profile, hard, twin, mixed-rigid and NET duplicate liabilities
without double counting.

## 1. Prior session continuation validated

`JSP000404Research.ProjectiveGapScaling` kernel build
[CI #39449929773](https://github.com/Charlie-Wang-03/awards/actions/runs/39449929773)
**PASS**, 8944 Lake steps; the four explicitly printed axioms lists are
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
The scaled one-dimensional cyclic gap budget and occupied integer-band
capacity are independently proven, as recorded in
`JSP000404_CYCLIC_DELETION_AND_PLANAR_N1_CHECKPOINT_2026-10-20.md`.

## 2. Actual geometric centre-to-Boolean-band bridge now kernel checked

`JSP000404Research.CentreProjectiveBandBudget` repaired:
- `scaledCentreAngles`, `centreFloorBandList` correctly noncomputable;
- typed `OtherVertex i` witnesses and ray-band list membership;
- sorted-angle pairwise transport across scaling;
- induction-exposed list constructor equalities and final floor list rewrite;
- `lam` binder shadowing across actual `AngleCap` and partition construction;
- explicit cardinal bound `occupiedProjectiveBands.card <= n+1`.

[CI #39456084980](https://github.com/Charlie-Wang-03/awards/actions/runs/39456084980)
**PASS**, 8956 Lake steps, no `sorryAx` for all its printed axioms.

Concrete statements:
```text
centreExponent C t <=
  (n+1) - (occupiedProjectiveBands hp t n i).card

(BinaryEdgePartition.active
    (projectiveBandPartition hp hcap htpos hlam n htop) i).card
  <= (n+1) - centreExponent (C i) t
```
These hold on the ACTUAL projective ray-cycle exponent and ACTUAL edge
partition, not on hypothetical credit allocations. They are local bounds,
not the missing global factor-two improvement.

## 3. Genuine n=2, four original centres, no top-exponent branch

`ProjectionOrdered.planar_lower_branch_n_two_four_no_top_capacity`
in `PlanarLowerTwoFourNoTopCapacity.lean`:
for n=2, |V|=4 and all actual centre exponents unequal to 1,
the standard concrete bound `centreExponent<2` forces every exponent
to zero, yielding sum(2^exponent)=4=2^2.
[CI #39455495174](https://github.com/Charlie-Wang-03/awards/actions/runs/39455495174)
**PASS**, 3506 jobs; axioms `[propext, Classical.choice, Quot.sound]`.
The no-top premise is a real extra restriction and is NOT known to follow
from the planar AngleCap assumption for all four-centre configurations.

Integrated that certified subcase into
`PlanarLowerBranchProofAdmittedWIP.lean`, commit
[`5cc16ac7c19882c4b53f8f49a707996962c7cc4c`](https://github.com/Charlie-Wang-03/awards/commit/5cc16ac7c19882c4b53f8f49a707996962c7cc4c).
Thus the sole admitted remainder additionally excludes the n=2/four/no-top
subcase. Root-WIP dedicated build checks were still running at checkpoint
time; this file does **not** claim those checks have passed.

## 4. Arbitrary-cut local budget: pending dependency repair

To explore whether movable projective cuts tighten the global payment,
created `.github/workflows/jsp000404-focused-cut-projective-band-budget.yml`
to build `JSP000404Research.CutProjectiveBandBudget`.
Initial failure [CI #39456500281](https://github.com/Charlie-Wang-03/awards/actions/runs/39456500281)
originated in `CutProjectiveBandPartition.lean`, not in the target module.
Changes made include correct noncomputability, division nonnegativity,
angle normalization, explicit sign-flip pi-rotation, correcting the
`AngleCap` lambda binder scope, classical bit decidability, and
explicit symmetric inequality. Follow-up CI pending.
NO claim that the arbitrary-cut chain is closed yet.

## 5. Unchanged proof boundary

- Global six-source nonreused payment is not proven.
- Whole-tree Fast Incremental Lean still has historical failures in
  other modules (e.g. residual colouring and narrow-cluster files).
- A Lean theorem with a conditional no-top premise or a local cut
  capacity does not eliminate the single root global `sorry`.
- Source-closure gate independently remains OPEN.
