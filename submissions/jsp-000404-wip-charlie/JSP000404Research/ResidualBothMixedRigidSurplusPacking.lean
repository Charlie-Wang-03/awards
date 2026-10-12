import JSP000404Research.ResidualDescendingRigidExactDebt
import Mathlib.Tactic

/-!
# Simultaneous payment for both orientations of mixed rigid carriers

P: old fully surplus-paid hard carriers.
A: excluded ascending rigid pairs (strict lower, saturated upper).
B: excluded descending rigid pairs (saturated lower, strict upper).

The three families are disjoint, and their union is a submatching
of all hard residual carrier edges. Therefore ALL local charges
   face_mass on P,
   lower_surplus on A,
   upper_surplus on B
fit within the ORIGINAL total dyadic surplus, WITHOUT REUSE.

The exact residual rigid debts are a lower target weight for A and
an upper target weight for B. This is an unconditional combinatorial
payment statement for ordered edge colourings, NOT a completed
planar dyadic capacity theorem.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

theorem paidHard_ascending_descending_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (surplusPayableHardCarrierPairs C exponent)
      (ascendingUnpaidRigidCarriers C exponent ∪
        descendingUnpaidRigidCarriers C exponent) ∧
    Disjoint (ascendingUnpaidRigidCarriers C exponent)
      (descendingUnpaidRigidCarriers C exponent) := by
  have hPA := paidHard_ascendingRigid_disjoint C exponent
  have hBP := (descendingRigid_disjoint_paid_and_ascending C exponent).1
  have hBA := (descendingRigid_disjoint_paid_and_ascending C exponent).2
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hright
    rcases Finset.mem_union.mp hright with ha | hb
    · exact (Finset.disjoint_left.mp hPA) hp ha
    · exact (Finset.disjoint_left.mp hBP) hb hp
  · exact hBA.symm

/-- Fully paid hard-overlap faces plus BOTH mixed rigid partial
surplus reservations fit simultaneously in the total surplus. -/
theorem paid_hard_and_both_mixed_rigid_credits_le_total_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (surplusPaidHardOverlapWords C exponent).card +
      (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
        dyadicProfileSurplus exponent (projectedFree C) p.1) +
      (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
        dyadicProfileSurplus exponent (projectedFree C) p.2)
      ≤ totalDyadicProfileSurplus exponent (projectedFree C) := by
  classical
  let P := surplusPayableHardCarrierPairs C exponent
  let A := ascendingUnpaidRigidCarriers C exponent
  let B := descendingUnpaidRigidCarriers C exponent
  let S := P ∪ (A ∪ B)
  let g : V → ℕ :=
    dyadicProfileSurplus exponent (projectedFree C)
  let charge : V × V → ℕ := fun p =>
    if p ∈ P then (carrierOverlapWords C p).card
    else if p ∈ A then g p.1 else g p.2
  have hdisjoint :=
    paidHard_ascending_descending_disjoint C exponent
  have hS : S ⊆ hardOverlapCarrierPairs C := by
    intro p hp
    rcases Finset.mem_union.mp hp with hP | hAB
    · exact ((mem_surplusPayableHardCarrierPairs C exponent p).1 hP).1
    · rcases Finset.mem_union.mp hAB with hA | hB
      · exact ((mem_rigidHardOverlapCarrierPairs C p).1
          ((mem_ascendingUnpaidRigidCarriers C exponent p).1 hA).1).1
      · exact ((mem_rigidHardOverlapCarrierPairs C p).1
          ((mem_descendingUnpaidRigidCarriers C exponent p).1 hB).1).1
  have hlocal :
      ∀ p ∈ S, charge p ≤ g p.1 + g p.2 := by
    intro p hp
    by_cases hP : p ∈ P
    · simpa only [charge, if_pos hP] using
        surplusPayableHardCarrier_face_le_pair_surplus C exponent hP
    · by_cases hA : p ∈ A
      · simp only [charge, if_neg hP, if_pos hA]
        omega
      · simp only [charge, if_neg hP, if_neg hA]
        omega
  have hbudget :=
    hard_matching_arbitrary_charge_le_total_surplus
      C exponent S charge hS hlocal
  have hPSum :
      (∑ p ∈ P, charge p) =
        ∑ p ∈ P, (carrierOverlapWords C p).card := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [charge, if_pos hp]
  have hASum :
      (∑ p ∈ A, charge p) = ∑ p ∈ A, g p.1 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hnotP : p ∉ P :=
      ((mem_ascendingUnpaidRigidCarriers C exponent p).1 hp).2.1
    simp only [charge, if_neg hnotP, if_pos hp]
  have hBSum :
      (∑ p ∈ B, charge p) = ∑ p ∈ B, g p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hnotP : p ∉ P :=
      ((mem_descendingUnpaidRigidCarriers C exponent p).1 hp).2.1
    have hnotA : p ∉ A := by
      intro ha
      exact (Finset.disjoint_left.mp hdisjoint.2) ha hp
    simp only [charge, if_neg hnotP, if_neg hnotA]
  have hSum :
      (∑ p ∈ S, charge p) =
        (∑ p ∈ P, charge p) +
          ((∑ p ∈ A, charge p) +
            (∑ p ∈ B, charge p)) := by
    change (∑ p ∈ P ∪ (A ∪ B), charge p) = _
    rw [Finset.sum_union hdisjoint.1,
      Finset.sum_union hdisjoint.2]
  rw [hSum, hPSum, hASum, hBSum] at hbudget
  rw [surplusPaidHardOverlapWords_card_eq_carrier_mass]
  simpa only [Nat.add_assoc] using hbudget

/-- Both partial reservations remove precisely their corresponding
local surplus. The total rigid-mixed overlap mass is the credits
plus the sum of target weights at the respective strict endpoints. -/
theorem both_mixed_rigid_overlap_mass_eq_credits_add_debts
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
      (carrierOverlapWords C p).card) +
    (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
      (carrierOverlapWords C p).card) =
    ((∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
      dyadicProfileSurplus exponent (projectedFree C) p.1) +
     (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
      dyadicProfileSurplus exponent (projectedFree C) p.2)) +
    ((∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
      2 ^ exponent p.1) +
     (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
      2 ^ exponent p.2)) := by
  have hA := ascending_rigid_mass_eq_partial_credit_add_target
    C exponent
  have hB := descending_rigid_mass_eq_partial_credit_add_target
    C exponent
  omega

#print axioms paidHard_ascending_descending_disjoint
#print axioms paid_hard_and_both_mixed_rigid_credits_le_total_surplus
#print axioms both_mixed_rigid_overlap_mass_eq_credits_add_debts

end OrderedEdgeColoring
end JSP000404Research
