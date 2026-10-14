# JSP-000404 — Global NET/TWIN original-vertex budget and planar dyadic liability

Research date: 2026-10-14.
Branch: `research/jsp-000404-sharp-centre`.
Status: **partial mathematical progress only**. Full JSP-000404 open; the one admitted six-source global payment `sorry` in `PlanarLowerBranchProofAdmittedWIP.lean` remains.

## Independently kernel-checked mathematics

### A. Any number of original vertices (verified)

If the exact actual NET collision source-to-diagonal map has positive duplicate debt
`E_D > 0`, and `T` is the collection of actual terminal equal-exponent TWIN
rigid hard carriers, then

    8 + 2 * |T| <= |V|.
    Equivalently |T| + 4 <= floor(|V| / 2).

This is derived from a SAME-TARGET pair of distinct actual NET sources.
The pair requires exactly four distinct hard carriers (two forward, two
strict reverse), all disjoint from TWIN carriers. The union injects into
the single matching of actual original HARD carrier pairs. This does
**not** falsely add the costs of sources with DIFFERENT target diagonals.

Lean modules:
- `ResidualNetCollisionTwinGlobalVertexBudget.lean`
  - `net_collision_positive_duplicate_twin_global_vertex_budget`
  - `net_collision_positive_duplicate_twin_card_plus_four_le_half`
- `PlanarNetGlobalTwinBudget.lean`
  - `planar_net_global_duplicate_or_twin_vertex_budget`

Actual focussed CI (explicit targets, no root umbrella):
https://github.com/Charlie-Wang-03/awards/actions/runs/38560021641

Result: **SUCCESS**, 3,473 jobs. All 3 theorem axiom audits:
`[propext, Classical.choice, Quot.sound]`; NO `sorryAx`.

### B. True planar AngleCap at most eleven centres (verified)

For real projected planar AngleCap configurations, `|V|<=11`,
and positive actual `E_D`, the previously proved carrier cardinal cap
`|T|<=1` combines with geometric `k(v)<n` to yield

    SUM_(p in T) 2 ^ k(p.second) <= 2 ^ (n-1).

This is a dyadic **liability cap**, NOT newly unreserved surplus.

Lean modules:
- `ResidualNetCollisionElevenCentreTwinMass.lean`
  - `net_collision_positive_duplicate_eleven_centres_twin_mass_le`
- `PlanarNetElevenCentreTwinMass.lean`
  - `planar_net_eleven_centres_duplicate_or_twin_mass_le`

Focussed CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38560808223

Result: **SUCCESS**, 3,473 jobs; both `#print axioms` contain only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

### C. Simultaneous target fibre/TWIN budget (VERIFIED)

In `ResidualNetCollisionTwinAdjustedFibre.lean` the REAL target fibre
and the actual TWIN hard carrier family consume one shared
original-vertex matching:

    4 * |F_d| + 2 * |T| <= |V|    for EVERY target d.

This gives the exact capacity and global finite target ledger:

    |F_d| <= floor((|V| - 2*|T|)/4);
    E_D <= SUM_(d in distinct actual diagonal image)
                 (floor((|V| - 2*|T|)/4) - 1).

All arithmetic is natural-number arithmetic, with truncated subtraction.
The pointwise bound is strictly more informative than a vertex-quarter
cap when extra TWIN hard carrier ownership reduces available vertices.

Independent focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38561321399

Result: **SUCCESS**, 3,471 jobs. Three newly proved declarations:
- `net_collision_fibre_twin_joint_vertex_budget`
- `net_collision_fibre_card_le_twin_adjusted_quarter`
- `net_collision_duplicate_debt_le_twin_adjusted_quarter_excess`

All 3 `#print axioms`:
`[propext, Classical.choice, Quot.sound]`, NO `sorryAx`.

### D. Target-exact coloured-slot matching with TWIN vertex reservation (VERIFIED)

`ResidualNetCollisionTwinMatchingJointPayment.lean` proves:

    |F_d| <= min(nu_coloured_slot(G_d), floor((|V|-2*|T|)/4)).

It transports this source-fibre cap into the exact NET duplicate-image
debt sum and actual mobile hard-source ledger, preserving the TRUE
Boolean holes vs already-COVERED target blocker distinction.

Focused Lean CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38562709753

Result **SUCCESS**: 3,472 jobs, 4 audited declarations;
axioms are exactly [propext, Classical.choice, Quot.sound].

### E. Source-native ORIGINAL bridge matching with TWIN reservation (VERIFIED)

**New theorem:** `ResidualNetCollisionOriginalTwinJointCapacity.lean`.
With `mu_original(d)` the maximum number of eligible SOFT
target-exact bridges using pairwise vertex-disjoint ORIGINAL centres,
not merely separate coloured endpoint slots:

    |F_d| <= min(mu_original(d), floor((|V|-2*|T|)/4)).

This is independently formally established **no weaker than BOTH**:
- `min(nu_coloured_slot(d), floor((|V|-2*|T|)/4))`
- `min(mu_original(d), floor(|V|/4))`

The exact diagonal-image excess sum and mobile source budget inherit
the stronger bound. The full mobile bound continues to track actual
singleton words, actual soft words, literal Boolean holes, distinct
already-COVERED diagonal blockers, and duplicate-image excess separately.

Kernel-checked declarations:

- `net_collision_fibre_original_matching_twin_reserved_min`
- `net_collision_original_twin_min_le_slot_twin_min`
- `net_collision_original_twin_min_le_original_quarter_min`
- `net_collision_duplicate_debt_le_original_twin_matching_excess`
- `net_mobile_mass_le_holes_covered_original_twin_matching_excess`

Focused GitHub Actions CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38578187635

Result **SUCCESS**, 3,473 jobs, zero Lean errors.
All five #print axioms checks:
[propext, Classical.choice, Quot.sound]. NO sorryAx.

The improvement is a pointwise bound on ACTUAL source fibres, not a
claim of globally non-reusable targetwise carrier or true-hole payments.
Even if the new bound is strictly smaller for a target, that alone does
not prove global six-source dyadic capacity, since soft, twin,
mixed-rigid and projected profile loss liabilities remain outstanding.


### F. Root import-chain repairs without introducing proof holes

Historical root entry `JSP000404Research.lean` remains NOT green. The
full fast CI contains many unrelated legacy errors; separate certified
frontier modules MUST NOT be downgraded because of those errors, and
neither should they be presented as a fully green root tree.

An actual **logical prerequisite** was repaired in
`BinaryMissingDefect.lean`: an old tactic step tried to infer

    |V| + |Q| <= 2^k

from `|Q| <= D` and `D <= 2^k - |V|` using Nat truncated
subtraction WITHOUT first establishing `|V|<=2^k`.
The correct proof derives the missing baseline capacity from
`weighted_hansel bit specified hsep`, then uses the truncated defect
inequality. No new mathematical assumption, sorry or axiom is added.

Focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38580323522

Result: **SUCCESS**, 3,095 jobs, zero Lean errors;
`weighted_hansel_missing_finset` and its two
`BinaryEdgePartition` corollaries are kernel-checked and free of
`sorryAx`.

A stale Mathlib import `Mathlib.Data.Matrix.Notation` in
`SupportIntervalCertificate.lean` was replaced with
`Mathlib.Data.Matrix.Basic`. This fixes the observed invalid import,
but the independent support-interval run
https://github.com/Charlie-Wang-03/awards/actions/runs/38580724431
has now completed **FAILURE**. It exposed six previously masked
elaboration errors in dependency `ConcreteTransitionInterval.lean`
(lines 81, 121-122, 226, 279 and 307), including an AngleCap
`lam` parameter mismatch, removed `List.length_eq_zero.mp`,
list-expression rewrite shape drift, and a wrong
`div_pos_iff` branch elimination. `SupportIntervalCertificate.lean`
itself is therefore NOT yet kernel-verified at the new HEAD.
Do not represent this chain as repaired or the root umbrella as green.


## Integrity and outstanding geometric obligation

1. Local source-fibre multiplicity, hard carrier matching and TWIN dyadic
   upper bounds count ACTUAL objects. They are **not** non-reusable Boolean
   hole credits or unused dyadic profile surplus.
2. Full six-source payment still has true Boolean hole vs ALREADY COVERED
   diagonal distinctions, fifth-centre blockers, soft overlap,
   terminal TWIN mass, both mixed-rigid classes and projected loss.
3. Different target fibres can reuse original carriers; summing raw
   per-target vertex consumption is invalid without a disjoint-allocation
   theorem. The above results do not make that erroneous step.
4. `JSP000404Research.lean` imports a large HISTORICAL umbrella collection
   with hundreds of unrelated elaboration failures. It is NOT fully green.
   Keep isolated kernel-verified frontier separate from historical root
   compilation debt, and do not claim an unrestricted proof.

## Next non-admitted mathematical proof

Prove a geometry-correct, genuinely GLOBAL non-reusing payment assignment
from actual collision sinks (and separately terminal rigid/mixed/soft/loss
liabilities) into literal TRUE Boolean holes and dyadic surplus proven
UNRESERVED by all prior carrier allocations. Work with distinct actual
targets and fifth-centre blocker witnesses; do not equate a bound on
candidate bridge/matching capacities with payment.
