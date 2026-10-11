import JSP000404Research.ResidualUnpaidRigidPartialReservation
import JSP000404Research.ResidualSaturatedHardRemainder
import Mathlib.Tactic

/-!
# Exact net-payment reduction after partial rigid-face reservations

The whole-face hard payments are already excluded from unpaidHardOverlapWords.
Now select the further unreserved RIGID pairs with strictly slack lower
endpoint and saturated upper endpoint, and reserve their LOWER surplus.

For every such ascending rigid carrier, the actual full Boolean overlap
mass is LOWER SURPLUS plus LOWER TARGET WEIGHT. Hard carrier uniqueness
means the full overlap faces are disjoint globally.

The remaining dyadic payment is therefore equivalent to paying:
  * soft completion overlaps;
  * unpaid hard words from all NON-ascending carriers;
  * one LOWER target weight per ascending rigid carrier;
  * projected-profile loss;
against true Boolean holes plus surplus NET of BOTH payment reservations.

The new global partial reservation is kernel-certified, so no surplus
is double-counted. The resulting inequality remains unproved from
planar geometry. This module adds NO sorry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

noncomputable def ascendingUnpaidRigidWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (ascendingUnpaidRigidCarriers C exponent).biUnion
    (carrierOverlapWords C)

/-- Ascending rigid faces selected for partial surplus payment are
ACTUAL unpaid hard words, and no word from the previous full-face
reservation can belong to one of these faces. -/
theorem ascendingUnpaidRigidWords_subset_unpaidHard
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    ascendingUnpaidRigidWords C exponent ⊆
      unpaidHardOverlapWords C exponent := by
  classical
  intro word hw
  obtain ⟨p,hp,hpw⟩ := Finset.mem_biUnion.mp hw
  have h := (mem_ascendingUnpaidRigidCarriers C exponent p).1 hp
  have hhard : p ∈ hardOverlapCarrierPairs C :=
    ((mem_rigidHardOverlapCarrierPairs C p).1 h.1).1
  have hpord : p.1 < p.2 :=
    ((mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hhard).1).1).1
  have hwordHard : word ∈ hardOverlapCompletionWords C := by
    unfold hardOverlapCompletionWords
    exact Finset.mem_biUnion.mpr ⟨p,hhard,hpw⟩
  have hnotPaid : word ∉ surplusPaidHardOverlapWords C exponent := by
    intro hpaid
    obtain ⟨q,hq,hqw⟩ := Finset.mem_biUnion.mp hpaid
    have hqhard : q ∈ hardOverlapCarrierPairs C :=
      ((mem_surplusPayableHardCarrierPairs C exponent q).1 hq).1
    have hqord : q.1 < q.2 :=
      ((mem_residualCarrierPairs C q.1 q.2).1
        ((mem_overlapCarrierPairs C q).1
          ((mem_hardOverlapCarrierPairs C q).1 hqhard).1).1).1
    obtain ⟨hfirst, hsecond⟩ :=
      completion_word_unique_ordered_pair C hpord hqord
        (Finset.mem_inter.mp hpw).1
        (Finset.mem_inter.mp hpw).2
        (Finset.mem_inter.mp hqw).1
        (Finset.mem_inter.mp hqw).2
    have hpq : p = q := Prod.ext hfirst hsecond
    have hpPaid : p ∈ surplusPayableHardCarrierPairs C exponent := by
      simpa only [hpq] using hq
    exact h.2.1 hpPaid
  exact Finset.mem_sdiff.mpr ⟨hwordHard, hnotPaid⟩

/-- Distinct selected ascending rigid carriers own disjoint Boolean
overlap faces; their aggregate overlap cardinality is EXACT. -/
theorem ascendingUnpaidRigidWords_card_eq_mass
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (ascendingUnpaidRigidWords C exponent).card =
      ∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
        (carrierOverlapWords C p).card := by
  classical
  have hpair :
      ((ascendingUnpaidRigidCarriers C exponent :
        Finset (V × V)) : Set (V × V)).PairwiseDisjoint
        (carrierOverlapWords C) := by
    intro p hp q hq hpq
    apply carrierOverlapWords_pairwiseDisjoint C
    · have hrigid :=
        ((mem_ascendingUnpaidRigidCarriers C exponent p).1
          (by simpa using hp)).1
      have hhard := ((mem_rigidHardOverlapCarrierPairs C p).1 hrigid).1
      exact ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hhard).1).1
    · have hrigid :=
        ((mem_ascendingUnpaidRigidCarriers C exponent q).1
          (by simpa using hq)).1
      have hhard := ((mem_rigidHardOverlapCarrierPairs C q).1 hrigid).1
      exact ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 hhard).1).1
    · exact hpq
  unfold ascendingUnpaidRigidWords
  exact Finset.card_biUnion hpair

/-- The originally unpaid hard words partition into the selected
ascending rigid Boolean faces and ALL other unpaid hard words. -/
theorem unpaidHard_card_eq_ascending_add_other
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (unpaidHardOverlapWords C exponent).card =
      (ascendingUnpaidRigidWords C exponent).card +
        (unpaidHardOverlapWords C exponent \
          ascendingUnpaidRigidWords C exponent).card := by
  have hsub := ascendingUnpaidRigidWords_subset_unpaidHard C exponent
  rw [Finset.card_sdiff_of_subset hsub]
  have hle := Finset.card_le_card hsub
  omega

/-- For ALL selected ascending rigid faces together, exact
overlap cardinality = separately reserved lower surplus
+ aggregate lower target-weight debt. -/
theorem ascendingUnpaidRigidWords_card_eq_credit_add_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (ascendingUnpaidRigidWords C exponent).card =
      (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
        dyadicProfileSurplus exponent (projectedFree C) p.1) +
      (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
        2 ^ exponent p.1) := by
  rw [ascendingUnpaidRigidWords_card_eq_mass]
  exact ascending_rigid_mass_eq_partial_credit_add_target C exponent

/-- This is the NEW, exact residual debt equivalence. All already
spent surplus is deducted from the RHS. The remaining "ascending"
charge is only the lower target weight, not its entire overlap face.
Neither side is asserted to hold without geometric input. -/
theorem completion_defect_payment_iff_after_ascending_partial_credit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    ((softOverlapCompletionWords C).card +
      (unpaidHardOverlapWords C exponent).card +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          (totalDyadicProfileSurplus exponent (projectedFree C) -
            (surplusPaidHardOverlapWords C exponent).card))
    ↔
    ((softOverlapCompletionWords C).card +
      (unpaidHardOverlapWords C exponent \
        ascendingUnpaidRigidWords C exponent).card +
      (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
        2 ^ exponent p.1) +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          (totalDyadicProfileSurplus exponent (projectedFree C) -
            (surplusPaidHardOverlapWords C exponent).card -
            (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
              dyadicProfileSurplus exponent (projectedFree C) p.1))) := by
  have hsplit := unpaidHard_card_eq_ascending_add_other C exponent
  have hmass :=
    ascendingUnpaidRigidWords_card_eq_credit_add_target C exponent
  have hnet :=
    paid_hard_mass_add_ascending_rigid_partial_le_total_surplus
      C exponent
  omega

#print axioms ascendingUnpaidRigidWords_subset_unpaidHard
#print axioms ascendingUnpaidRigidWords_card_eq_mass
#print axioms ascendingUnpaidRigidWords_card_eq_credit_add_target
#print axioms completion_defect_payment_iff_after_ascending_partial_credit

end OrderedEdgeColoring
end JSP000404Research
