# JSP-000404 — Target-exact shell slots and rigorous mobile payment refinement

Date: 2026-10-14. Branch: `research/jsp-000404-sharp-centre`.

Status: **11 NEW SORRY-FREE THEOREMS VERIFIED / SIX-SOURCE GLOBAL PAYMENT OPEN**.

## Mathematical improvement

Earlier a given canonical target `d` was allocated an original
source-compatible bridge pool `B_2(d)`, a lower endpoint-plus-inactive-colour
slot pool `L(d)`, and an upper endpoint-plus-inactive-colour slot pool
`U(d)`. Each actual NET collision source whose chosen diagonal equals
`d` injects into each candidate pool.

The earlier coarse slot definitions admitted ANY inactive colour at an
eligible bridge endpoint, even when that colour was unrelated to the
canonical target's exact violation at the **OTHER** endpoint.

The two new pools remove such impossible slot assignments:

- `L*(d)`: lower endpoint `b` plus original reverse colour `cr`.
  It requires `cr` retained-inactive at `b` AND an eligible original
  bridge `(b,v) ∈ B_2(d)` such that
  `cr ∈ retainedActiveViolationCoords(C,v,d)`.
- `U*(d)`: upper endpoint `v` plus original forward colour `cf`.
  It requires `cf` retained-inactive at `v` AND an eligible original
  bridge `(b,v) ∈ B_2(d)` such that
  `cf ∈ retainedActiveViolationCoords(C,b,d)`.

The previous source-native exact-shell lemma guarantees the
violated-active-coordinate sets at the two original endpoints are
**singletons**, exactly the original colours `cf` and `cr`.
Therefore every TRUE ACTUAL NET source enters each new slot pool.
The fixed-target maps `s ↦ (lower(s),cr(s))` and
`s ↦ (upper(s),cf(s))` are individually injective. Consequently:

```text
|D^-1(d)| <= |L*(d)| <= |L(d)|
|D^-1(d)| <= |U*(d)| <= |U(d)|.

m*(d) := min(|B_2(d)|, |L*(d)|, |U*(d)|)
m(d)  := min(|B_2(d)|, |L(d)|,  |U(d)|)

|D^-1(d)| <= m*(d) <= m(d).
```

An inequality can be strict for configurations with inactive colours
that are not shell-compatible with any eligible opposite endpoint;
**strict improvement in all configurations is NOT claimed**.

## Exact globally non-reusing duplicate ledger

With `I` the genuine NET forward/reverse sink collision set and
`D : I → (Fin n → Bool)` the certified source-selected double-flip map,
the previously proved exact fibre identity and new sharp pointwise
capacity give:

```text
E_D := |I| - |D(I)|
     = Σ_(d∈D(I)) (|D^-1(d)|-1)
    <= Σ_(d∈D(I)) (m*(d)-1).
```

Moreover the **verified actual mobile-source bound** is:

```text
|NET forward hard| + |NET reverse strict rigid|
  <= |singleton covered| + |soft overlap covered|
   + |TRUE Boolean holes|
   + |DISTINCT already-covered canonical diagonals|
   + Σ_(d∈D(I)) (m*(d)-1).
```

The sum is indexed by distinct actual targets and retains the true-hole
versus covered-target separation. Every candidate bridge and exact
slot is merely a capacity constraint, **not** a literal Boolean
hole or a genuinely unreserved profile-surplus payment source.
The theorem `m*(d)<=1` for ALL actually attained targets would imply
`E_D=0`, but the real planar `AngleCap` premises are **not known
to imply this uniqueness**. The terminal-twin, both mixed-rigid,
soft-overlap, projected-loss, fifth-centre and cross-bridge
obstructions remain genuine.

## Checked Lean declarations

Module `JSP000404Research/ResidualNetCollisionExactShellColourSlots.lean`
contains six newly proved theorems:

1. `target_lower_exact_shell_slots_subset_coarse`
2. `target_upper_exact_shell_slots_subset_coarse`
3. `net_collision_actual_lower_exact_slot_mem`
4. `net_collision_actual_upper_exact_slot_mem`
5. `net_collision_target_fibre_card_le_lower_exact_shell_slots`
6. `net_collision_target_fibre_card_le_upper_exact_shell_slots`

CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38494390479
**PASS**, 3,267 Lean jobs; all six `#print axioms` outputs omit `sorryAx`.

Module `JSP000404Research/ResidualNetCollisionExactShellPaymentBound.lean`
contains five further proved theorems:

1. `net_collision_diagonal_fibre_card_le_exact_shell_joint_min`
2. `net_collision_exact_shell_joint_capacity_le_coarse_joint`
3. `net_collision_duplicate_debt_le_sum_exact_shell_joint_excess`
4. `net_collision_duplicate_debt_zero_of_exact_shell_joint_unique`
5. `net_mobile_mass_le_holes_covered_exact_shell_joint_excess`

CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38494699064
**PASS**, 3,268 Lean jobs; all five `#print axioms` outputs omit `sorryAx`.

A real Lean failure from opaque function-projection equality rewriting
was repaired using explicit `change` to normalize original colour
equalities; no new axioms, new `sorry` or weakened proof statement
were introduced.

Both modules are imported into the fully independent
`VerifiedOverlapRewire.lean` and the separate
`PlanarLowerBranchProofAdmittedWIP.lean`; the latter retains its
single, explicitly audited admitted global payment inequality.

## Next research obligation

Either establish actual `AngleCap` restrictions that exclude
cross-bridge same-target repeated hits for this target-exact shell
structure, OR prove a true non-reusing global compensation for the
remaining excess and genuine fifth-centre covered targets using
literal global Boolean holes and independently UNRESERVED dyadic
profile surplus, while paying terminal twin, mixed rigid, soft,
and projected loss. Neither has been proved here.

Full JSP-000404 remains neither proved nor disproved.
