# JSP-000404 — Lean repair and conditional-capacity checkpoint

Date: 2026-10-16. Research branch: `research/jsp-000404-sharp-centre`.

**Problem status: OPEN.** This checkpoint is not a complete mathematical
proof or disproof. The source-closure gate is also still OPEN.
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` retains its
single executable `sorry`, whose genuine unresolved input is a GLOBAL
non-reusing payment of original terminal debts and translated-loss
duplicates by Boolean true holes OUTSIDE the translated-loss union
and genuinely unreserved surplus.

## Certified Lean repairs

### 1. Common-dominator minimum phase covers

Source: `JSP000404Research/MinimumDominatingPhaseCover.lean`.

The proof now handles the witness from `Nat.find`, strict decreases of
a finite cover after erasure, and reversal of a distinctness hypothesis
without relying on an invalid `.symm` projection.

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38855787098
**SUCCESS** (3,096 jobs). Axiom audits on all four declarations have
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`.

Especially, `slot_injective_on_minimum_cover_of_common_dominator`
proves that a minimum-cardinality cover cannot contain two distinct
obstructions sharing a slot when each slot has a common dominator.
`no_phase_cover_of_common_dominator_turn_slots` then gives the
conditional global phase-cover contradiction.

### 2. Vertex-labelled binary Kraft certificate

Source: `JSP000404Research/LabeledBinaryKraftTree.lean`.

The module now proves the tree/profile depth and label identities,
handles the actual decidable finite-vertex type, fixes list/profile
reindexing, and explicitly specializes the bound on exponents before
using natural-subtraction arithmetic.

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38856107776
**SUCCESS** (3,093 jobs). The audited
`LabeledBinaryKraftTree.Certificate.capacity` and
`LabeledBinaryKraftTree.Certificate.exponent_capacity` declarations
have no `sorryAx`.

The verified **conditional** theorem is:

```text
complete vertex-labelled full binary tree,
one distinct leaf for every vertex v,
leaf depth(v) <= ell(v) = n - exponent(v),
exponent(v) <= n
  => sum_v 2^exponent(v) <= 2^n.
```

An actual geometry-to-labelled-tree certificate satisfying this
depth budget has NOT been constructed from the original planar
hypotheses; its absence prevents promotion to an unconditional
JSP-000404 theorem.

### 3. Saturated seam unit-subslot arithmetic

Source: `JSP000404Research/SaturatedSeamPhaseArithmetic.lean`.

The repaired proof uses a noncomputable real-valued floor-based index,
casts natural truncated subtraction into the reals only after proving
subtraction bounds, and preserves the shared symbol `s` when
applying linear arithmetic to the exact floor identity.

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38856207495
**SUCCESS** (3,216 jobs).
`saturated_wrap_failure_unit_subslot` uses only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

In the theorem's exact saturation and unsafe-seam hypotheses, put
`j = n - floor(z)`, `q = floor(s)`, `s = a + t - z`,
`t = n + delta`, `0 <= delta < 1`. It proves
`q >= 2`, `j < q` and the sharp window:

```text
j + s - q < t - z <= j + delta.
```

## Verification boundary and next mathematical step

These were **three separately kernel-checked modules**, not a complete
workspace build. The historical full Fast Incremental Lean workflow at
head `d019510c487014901924c65c42b61a9c5cf0d4a9`, run
https://github.com/Charlie-Wang-03/awards/actions/runs/38850840471,
FAILED with 384 Lean errors in 49 legacy modules. Focused successes
must not be represented as resolving those other errors; a new full
run requires separate verification.

The currently decisive unproved step remains the globally non-reusing
payment/matching between the actual terminal twin, mixed-rigid and
soft/collision loss debt events and the genuinely eligible
outside-translated true holes plus **unreserved** surplus. Exact
edge/word-multiplicity ledgers and local geometry restrictions alone
do not yield this matching. Neither the conditional Kraft certificate
nor the conditional phase-cover compression supplies that missing
geometric construction.

All new repaired theorems above are `sorry`-free and introduce no
new custom axioms. No complete-problem, eligibility, priority,
submission or award claim is made.
