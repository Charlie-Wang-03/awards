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

### D. Target-exact matching meets TWIN-reserved original ownership (PENDING)

New `ResidualNetCollisionTwinMatchingJointPayment.lean` intersects
the independently checked exact-shell candidate maximum matching
constraint with the bound in C:

    |F_d| <= min(nu(G_d), floor((|V|-2*|T|)/4)),

and substitutes its actual-target fibre excess into the original
mobile source ledger while separating TRUE Boolean holes from
already-covered diagonal blockers.

This is a **possible** further capacity tightening, not a newly
available hole/surplus payment. The source is not verified until
focused CI reports success:
https://github.com/Charlie-Wang-03/awards/actions/runs/38562709753

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
