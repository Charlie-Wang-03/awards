# JSP-000404 · Exact NET endpoint-colour-slot capacities (2026-10-14)

## Status and mathematical scope

**LOCAL SOURCE-NATIVE MULTIPLICITY REFINEMENT VERIFIED.**
**GLOBAL SIX-SOURCE NONREUSE PAYMENT AND ORIGINAL PLANAR JSP-000404 REMAIN OPEN.**

Branch: `research/jsp-000404-sharp-centre`.
This note supplements, rather than supersedes,
`BRIDGE_STRICT_LOWER_GAP_PROOF_FRONTIER_2026-10-12.md`
and `BRIDGE_CROSS_ROLE_AND_INACTIVE_FRONTIER_2026-10-13.md`.

The original NET canonical double-flip map `D : I -> (Fin n -> Bool)`
has already been verified injective within each actual original
soft bridge. Its positive duplicate debt `E_D = |I| - |D(I)|`
is exactly the sum of per-target genuine source fibre excesses,
not a licence to reclassify covered targets as TRUE Boolean holes.

## New verified theorem chain

The first new sorry-free module,
`JSP000404Research/ResidualNetCollisionFixedEndpointColourInjection.lean`,
proves four theorems:

- `net_collision_same_diagonal_lower_star_reverse_colour_injective`
- `net_collision_same_diagonal_upper_star_forward_colour_injective`
- `net_collision_lower_star_target_fibre_card_le_inactive`
- `net_collision_upper_star_target_fibre_card_le_inactive`

For fixed certified target `d` and original soft bridge lower endpoint
`b`, exact singleton active-violation rigidity fixes the source's
original FORWARD flip colour. The other, original REVERSE colour is
inactive at `b` and uniquely tags each distinct ACTUAL source in the
fibre. The upper-endpoint construction is dual.

Writing `I(c) := (Finset.univ : Finset (Fin n)) \ retainedActive(C,c)`:

```text
|{s in genuine NET | D(s)=d and B(s).lower=b}| <= |I(b)|
|{s in genuine NET | D(s)=d and B(s).upper=v}| <= |I(v)|.
```

These are LINEAR in inactive completion dimension, not the
`2^|I(c)|` whole-cube cardinality.

The second new sorry-free module,
`JSP000404Research/ResidualNetCollisionTargetBridgeColourSlots.lean`,
proves SIX theorems:

- `net_collision_diagonal_fibre_card_le_lower_target_colour_slots`
- `net_collision_diagonal_fibre_card_le_upper_target_colour_slots`
- `net_collision_duplicate_debt_le_sum_lower_colour_slot_excess`
- `net_collision_diagonal_fibre_card_le_joint_bridge_slot_min`
- `net_collision_duplicate_debt_le_sum_joint_bridge_slot_excess`
- `net_collision_duplicate_debt_zero_of_joint_capacity_at_most_one`

For fixed target d, let `B_2(d)` be the earlier genuine-source-compatible
double-shell candidate SOFT bridge pool. Define `L(d)` to be pairs
`(b,cr)` where `b` is the lower endpoint of SOME bridge in
`B_2(d)` and `cr` is INACTIVE at `b`; define `U(d)` dually
as `(v,cf)`.

An ACTUAL source with target d maps INJECTIVELY to
`(its original lower vertex, its original reverse colour)`, and
also to `(its original upper vertex, its original forward colour)`.
Hence the kernel now proves the joint, pointwise and global bounds:

```text
|D^-1(d)| <= m(d) := min(|B_2(d)|, |L(d)|, |U(d)|)

E_D = |I| - |D(I)|
    = sum_(d in D(I)) (|D^-1(d)| - 1)
   <= sum_(d in D(I)) (m(d) - 1).
```

This preserves each target's own excess and does not multiply a
lower vertex's inactive-colour slots by its many SOFT candidate
neighbours. An additional theorem proves the CONDITIONAL statement:
if `m(d)<=1` for every ACTUALLY HIT d, then `E_D=0`.
No theorem currently derives that hypothesis from planar AngleCap.
Thus the original geometrically meaningful cross-bridge source
payment remains OPEN; an upper bound on COVERED candidate capacities
is not independently available hole/surplus credit.

## Proof engineering and CI evidence

- First module: https://github.com/Charlie-Wang-03/awards/actions/runs/38434467221
  3265 jobs PASS, 4 new kernel-proven theorems with no `sorryAx`.
- Second module: https://github.com/Charlie-Wang-03/awards/actions/runs/38435375400
  3266 jobs PASS, 6 new kernel-proven theorems with no `sorryAx`.

The first source had a Lean elaboration problem:
`rw [hcf,hcr]` could not rewrite a hidden lambda application in
the original colour-injection hypothesis. It was repaired by
explicitly exposing the evaluated colour equality with `change`.
No new axioms, `sorry`, `admit`, weakened statement or
synthetic source hypothesis was introduced.

## Remaining WIP frontier

Still needed: a **global, non-reusing** literal TRUE Boolean hole
and genuinely UNRESERVED dyadic profile-surplus payment for ALL SIX
source families, including target-duplicate and fifth-centre
covered diagonal debts, net forward/reverse hard sources, soft
overlap, terminal twin, ascending/descending mixed rigid, and
projected profile loss. Neither the existing endpoint slot
capacity nor the target-specific pool `B_2(d)` is a true-hole
count. The sole WIP `sorry` is deliberately retained.
