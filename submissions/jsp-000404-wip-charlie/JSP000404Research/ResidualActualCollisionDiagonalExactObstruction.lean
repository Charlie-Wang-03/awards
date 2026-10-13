import JSP000404Research.ResidualTwoFlipSourceEndpointBlocker
import JSP000404Research.ResidualTwoFlipOppositeBitBlocker
import Mathlib.Tactic

/-!
# Exact obstruction characterization for actual hard transport collisions

This module adds NO planar or Hall hypotheses.  At a collision between the
already-proved globally injective forward and reverse transports, the opposite
two-flip diagonal is covered iff one of the two original hard source endpoints
blocks the flip, or some centre outside the four original hard endpoints
covers it.  This is a local IFF, not the missing global hole payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- An actual collision diagonal is covered exactly by either source-side
cross-inactivity or by a fifth-or-later covering centre.  All alternatives
refer to the literal original hard transport data, without hypothetical
candidate bridge faces. -/
theorem actual_collision_diagonal_covered_iff_source_block_or_fifth
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1) :
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    let cf := transportablePairColor C p
    let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
    let w := (transportableHardWordToSingletonOrSoft C x).1
    let d := flipCompletionWord cf (flipCompletionWord cr w)
    d ∈ coveredCompletionWords C ↔
      (cr ∉ retainedActive C p.1.1 ∨
       cf ∉ retainedActive C q.1.2 ∨
       ∃ c : V, c ≠ p.1.1 ∧ c ≠ p.1.2 ∧
         c ≠ q.1.1 ∧ c ≠ q.1.2 ∧
         d ∈ retainedCompletionWords C c) := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let w := (transportableHardWordToSingletonOrSoft C x).1
  let d := flipCompletionWord cf (flipCompletionWord cr w)
  change d ∈ coveredCompletionWords C ↔
    (cr ∉ retainedActive C p.1.1 ∨
     cf ∉ retainedActive C q.1.2 ∨
     ∃ c : V, c ≠ p.1.1 ∧ c ≠ p.1.2 ∧
       c ≠ q.1.1 ∧ c ≠ q.1.2 ∧
       d ∈ retainedCompletionWords C c)
  constructor
  · intro hcovered
    by_cases ha : cr ∈ retainedActive C p.1.1
    · by_cases hz : cf ∈ retainedActive C q.1.2
      · right
        right
        exact actual_collision_covered_diagonal_has_fifth_centre
          C exponent hexp honeLoss x y hcollision ha hz hcovered
      · exact Or.inr (Or.inl hz)
    · exact Or.inl ha
  · intro h
    rcases h with ha | hz | ⟨c, _, _, _, _, hc⟩
    · have hlocal : d ∈ retainedCompletionWords C p.1.1 :=
        actual_collision_diagonal_covered_by_forward_lower_if_inactive
          C exponent hexp honeLoss x y hcollision ha
      exact (mem_coveredCompletionWords C d).2
        ⟨p.1.1, (mem_completionFibre C d p.1.1).2 hlocal⟩
    · have hlocal : d ∈ retainedCompletionWords C q.1.2 :=
        actual_collision_diagonal_covered_by_reverse_upper_if_inactive
          C exponent hexp honeLoss x y hcollision hz
      exact (mem_coveredCompletionWords C d).2
        ⟨q.1.2, (mem_completionFibre C d q.1.2).2 hlocal⟩
    · exact (mem_coveredCompletionWords C d).2
        ⟨c, (mem_completionFibre C d c).2 hc⟩

/-- Equivalently, a true global Boolean hole at an actual collision
diagonal requires BOTH source cross-activities and the absence of EVERY
fifth-or-later covering centre, and those conditions are sufficient.
This statement is local and does not assert a global injective allocation
of such holes across multiple collisions. -/
theorem actual_collision_diagonal_true_hole_iff_cross_active_no_fifth
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1) :
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    let cf := transportablePairColor C p
    let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
    let w := (transportableHardWordToSingletonOrSoft C x).1
    let d := flipCompletionWord cf (flipCompletionWord cr w)
    (d ∈ (Finset.univ : Finset (Fin n → Bool)) \
      coveredCompletionWords C) ↔
      (cr ∈ retainedActive C p.1.1 ∧
       cf ∈ retainedActive C q.1.2 ∧
       ∀ c : V, c ≠ p.1.1 → c ≠ p.1.2 →
         c ≠ q.1.1 → c ≠ q.1.2 →
         d ∉ retainedCompletionWords C c) := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let w := (transportableHardWordToSingletonOrSoft C x).1
  let d := flipCompletionWord cf (flipCompletionWord cr w)
  change (d ∈ (Finset.univ : Finset (Fin n → Bool)) \
    coveredCompletionWords C) ↔
    (cr ∈ retainedActive C p.1.1 ∧
     cf ∈ retainedActive C q.1.2 ∧
     ∀ c : V, c ≠ p.1.1 → c ≠ p.1.2 →
       c ≠ q.1.1 → c ≠ q.1.2 →
       d ∉ retainedCompletionWords C c)
  constructor
  · intro hhole
    have hcross :=
      actual_collision_diagonal_true_hole_requires_source_cross_activity
        C exponent hexp honeLoss x y hcollision
        (Finset.mem_sdiff.mp hhole).2
    have hiff :=
      actual_collision_diagonal_hole_iff_no_fifth_centre
        C exponent hexp honeLoss x y hcollision hcross.1 hcross.2
    exact ⟨hcross.1, hcross.2, hiff.mp hhole⟩
  · rintro ⟨ha, hz, hno⟩
    exact (actual_collision_diagonal_hole_iff_no_fifth_centre
      C exponent hexp honeLoss x y hcollision ha hz).2 hno


/-- In the exact covered-diagonal IFF, any FIFTH-centre obstruction
also carries a precise opposite retained-bit signature relative
to one of the two actual BRIDGE endpoints (reverse lower or
forward upper). This is necessary for coverage; it is not an
AngleCap-level theorem excluding such an obstruction. -/
theorem actual_collision_diagonal_covered_iff_source_block_or_opposite_fifth
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1) :
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    let cf := transportablePairColor C p
    let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
    let w := (transportableHardWordToSingletonOrSoft C x).1
    let d := flipCompletionWord cf (flipCompletionWord cr w)
    d ∈ coveredCompletionWords C ↔
      (cr ∉ retainedActive C p.1.1 ∨
       cf ∉ retainedActive C q.1.2 ∨
       ∃ c : V, c ≠ p.1.1 ∧ c ≠ p.1.2 ∧
         c ≠ q.1.1 ∧ c ≠ q.1.2 ∧
         d ∈ retainedCompletionWords C c ∧
         ((cr ∈ retainedActive C c ∧
           retainedBit C c cr = !(retainedBit C p.1.2 cr)) ∨
          (cf ∈ retainedActive C c ∧
           retainedBit C c cf = !(retainedBit C q.1.1 cf)))) := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let w := (transportableHardWordToSingletonOrSoft C x).1
  let d := flipCompletionWord cf (flipCompletionWord cr w)
  change d ∈ coveredCompletionWords C ↔
    (cr ∉ retainedActive C p.1.1 ∨
     cf ∉ retainedActive C q.1.2 ∨
     ∃ c : V, c ≠ p.1.1 ∧ c ≠ p.1.2 ∧
       c ≠ q.1.1 ∧ c ≠ q.1.2 ∧
       d ∈ retainedCompletionWords C c ∧
       ((cr ∈ retainedActive C c ∧
         retainedBit C c cr = !(retainedBit C p.1.2 cr)) ∨
        (cf ∈ retainedActive C c ∧
         retainedBit C c cf = !(retainedBit C q.1.1 cf))))
  have hbase :=
    actual_collision_diagonal_covered_iff_source_block_or_fifth
      C exponent hexp honeLoss x y hcollision
  change (d ∈ coveredCompletionWords C ↔
    (cr ∉ retainedActive C p.1.1 ∨
     cf ∉ retainedActive C q.1.2 ∨
     ∃ c : V, c ≠ p.1.1 ∧ c ≠ p.1.2 ∧
       c ≠ q.1.1 ∧ c ≠ q.1.2 ∧
       d ∈ retainedCompletionWords C c)) at hbase
  constructor
  · intro hcovered
    rcases hbase.mp hcovered with ha | hz | ⟨c, hca, hcv, hcb, hcz, hc⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inl hz)
    · right
      right
      have hbridge :=
        forward_reverse_collision_cross_active_flip_colors
          C exponent hexp honeLoss x y hcollision
      change cf ∈ retainedActive C q.1.1 ∧
        cr ∈ retainedActive C p.1.2 at hbridge
      have hcrInactiveB : cr ∉ retainedActive C q.1.1 :=
        (strictDescentRigidPairColor_spec
          C exponent hexp honeLoss q).2
      have hbv : q.1.1 ≠ p.1.2 := by
        intro heq
        apply hcrInactiveB
        rw [heq]
        exact hbridge.2
      have hwB : w ∈ retainedCompletionWords C q.1.1 := by
        change (transportableHardWordToSingletonOrSoft C x).1 ∈ _
        rw [hcollision]
        exact strictDescentRigidWordToSingletonOrSoft_mem_lower
          C exponent hexp honeLoss y
      have hwV : w ∈ retainedCompletionWords C p.1.2 :=
        transportableHardWordToSingletonOrSoft_mem_upper C x
      have hob :=
        two_flip_diagonal_external_blocker_opposite_bit
          C q.1.1 p.1.2 c cf cr w hbv hbridge.1
            hcrInactiveB hbridge.2 hwB hwV hc
      exact ⟨c, hca, hcv, hcb, hcz, hc, hob⟩
  · intro h
    apply hbase.mpr
    rcases h with ha | hz | ⟨c, hca, hcv, hcb, hcz, hc, _⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr ⟨c, hca, hcv, hcb, hcz, hc⟩)

#print axioms actual_collision_diagonal_covered_iff_source_block_or_opposite_fifth

#print axioms actual_collision_diagonal_covered_iff_source_block_or_fifth
#print axioms actual_collision_diagonal_true_hole_iff_cross_active_no_fifth

end OrderedEdgeColoring
end JSP000404Research
