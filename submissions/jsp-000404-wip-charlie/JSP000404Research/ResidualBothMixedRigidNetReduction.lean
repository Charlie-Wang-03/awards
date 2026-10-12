import JSP000404Research.ResidualBothMixedRigidSurplusPacking
import Mathlib.Tactic

/-!
# Exact Boolean-word net payment after BOTH mixed rigid partial credits

Following the whole-face paid hard carrier reservation, the new
ascending and descending unpaid rigid families are disjoint.
Each complete Boolean overlap face is uniquely owned and their
partial profile surplus payments are simultaneously non-reusing.

All remaining mixed rigid debt is exactly the target mass of the
respective strict endpoint, not the full rigid overlap cube.
A residual inequality with these debts and genuine Boolean holes
is exactly equivalent to the older global completion payment.

This module is a kernel-checkable reduction, NOT a proof of the
remaining planar geometry. There is no sorry here.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

noncomputable def descendingUnpaidRigidWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (descendingUnpaidRigidCarriers C exponent).biUnion
    (carrierOverlapWords C)

/-- A hard face whose carrier is not in the previous whole-face
paid family belongs to the actual unpaid hard Boolean word set. -/
theorem unpayable_hard_carrier_words_subset_unpaid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {p : V × V} {word : Fin n → Bool}
    (hp : p ∈ hardOverlapCarrierPairs C)
    (hnot : p ∉ surplusPayableHardCarrierPairs C exponent)
    (hw : word ∈ carrierOverlapWords C p) :
    word ∈ unpaidHardOverlapWords C exponent := by
  classical
  have hwordHard : word ∈ hardOverlapCompletionWords C := by
    unfold hardOverlapCompletionWords
    exact Finset.mem_biUnion.mpr ⟨p, hp, hw⟩
  have hpord : p.1 < p.2 :=
    ((mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hp).1).1).1
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
        (Finset.mem_inter.mp hw).1
        (Finset.mem_inter.mp hw).2
        (Finset.mem_inter.mp hqw).1
        (Finset.mem_inter.mp hqw).2
    have hpq : p = q := Prod.ext hfirst hsecond
    exact hnot (hpq ▸ hq)
  exact Finset.mem_sdiff.mpr ⟨hwordHard, hnotPaid⟩

/-- Every selected descending rigid face is an actually unpaid hard
Boolean word. These faces are not paid whole by the old reservation. -/
theorem descendingUnpaidRigidWords_subset_unpaidHard
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    descendingUnpaidRigidWords C exponent ⊆
      unpaidHardOverlapWords C exponent := by
  intro word hw
  obtain ⟨p,hp,hpw⟩ := Finset.mem_biUnion.mp hw
  have h := (mem_descendingUnpaidRigidCarriers C exponent p).1 hp
  have hhard : p ∈ hardOverlapCarrierPairs C :=
    ((mem_rigidHardOverlapCarrierPairs C p).1 h.1).1
  exact unpayable_hard_carrier_words_subset_unpaid
    C exponent hhard h.2.1 hpw

/-- Boolean words selected from ascending and descending rigid
families are disjoint: carrier ownership of each overlapped word
is unique, and the two carrier families are disjoint. -/
theorem ascending_descending_rigid_words_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (ascendingUnpaidRigidWords C exponent)
      (descendingUnpaidRigidWords C exponent) := by
  classical
  apply Finset.disjoint_left.mpr
  intro word ha hb
  obtain ⟨p,hp,hpw⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨q,hq,hqw⟩ := Finset.mem_biUnion.mp hb
  have hpHard : p ∈ hardOverlapCarrierPairs C :=
    ((mem_rigidHardOverlapCarrierPairs C p).1
      ((mem_ascendingUnpaidRigidCarriers C exponent p).1 hp).1).1
  have hqHard : q ∈ hardOverlapCarrierPairs C :=
    ((mem_rigidHardOverlapCarrierPairs C q).1
      ((mem_descendingUnpaidRigidCarriers C exponent q).1 hq).1).1
  have hpord : p.1 < p.2 :=
    ((mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hpHard).1).1).1
  have hqord : q.1 < q.2 :=
    ((mem_residualCarrierPairs C q.1 q.2).1
      ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 hqHard).1).1).1
  obtain ⟨hfirst, hsecond⟩ :=
    completion_word_unique_ordered_pair C hpord hqord
      (Finset.mem_inter.mp hpw).1
      (Finset.mem_inter.mp hpw).2
      (Finset.mem_inter.mp hqw).1
      (Finset.mem_inter.mp hqw).2
  have hpq : p = q := Prod.ext hfirst hsecond
  have hpB : p ∈ descendingUnpaidRigidCarriers C exponent := by
    simpa only [hpq] using hq
  exact (Finset.disjoint_left.mp
    (paidHard_ascending_descending_disjoint C exponent).2) hp hpB

/-- Each selected descending rigid carrier has one unique whole
Boolean face. The union cardinal is exactly the sum of face masses. -/
theorem descendingUnpaidRigidWords_card_eq_mass
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (descendingUnpaidRigidWords C exponent).card =
      ∑ p ∈ descendingUnpaidRigidCarriers C exponent,
        (carrierOverlapWords C p).card := by
  classical
  have hpair :
      ((descendingUnpaidRigidCarriers C exponent :
        Finset (V × V)) : Set (V × V)).PairwiseDisjoint
        (carrierOverlapWords C) := by
    intro p hp q hq hpq
    apply carrierOverlapWords_pairwiseDisjoint C
    · have hrigid :=
        ((mem_descendingUnpaidRigidCarriers C exponent p).1
          (by simpa using hp)).1
      have hhard := ((mem_rigidHardOverlapCarrierPairs C p).1 hrigid).1
      exact ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hhard).1).1
    · have hrigid :=
        ((mem_descendingUnpaidRigidCarriers C exponent q).1
          (by simpa using hq)).1
      have hhard := ((mem_rigidHardOverlapCarrierPairs C q).1 hrigid).1
      exact ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 hhard).1).1
    · exact hpq
  unfold descendingUnpaidRigidWords
  exact Finset.card_biUnion hpair

/-- The descending family contributes only its upper endpoint
target-weight debt after its upper-surplus credit is reserved. -/
theorem descendingUnpaidRigidWords_card_eq_credit_add_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (descendingUnpaidRigidWords C exponent).card =
      (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
        dyadicProfileSurplus exponent (projectedFree C) p.2) +
      (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
        2 ^ exponent p.2) := by
  rw [descendingUnpaidRigidWords_card_eq_mass]
  exact descending_rigid_mass_eq_partial_credit_add_target C exponent

/-- The two selected mixed-rigid Boolean families have an exact,
nonduplicated union mass equal to both partial credits plus
both strict-endpoint target-weight debts. -/
theorem bothMixedRigidWords_card_eq_credits_add_debts
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (ascendingUnpaidRigidWords C exponent ∪
      descendingUnpaidRigidWords C exponent).card =
      ((∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
          dyadicProfileSurplus exponent (projectedFree C) p.1) +
       (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
          dyadicProfileSurplus exponent (projectedFree C) p.2)) +
      ((∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
          2 ^ exponent p.1) +
       (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
          2 ^ exponent p.2)) := by
  rw [Finset.card_union_of_disjoint
    (ascending_descending_rigid_words_disjoint C exponent)]
  rw [ascendingUnpaidRigidWords_card_eq_credit_add_target,
      descendingUnpaidRigidWords_card_eq_credit_add_target]
  omega

/-- The mixed-rigid union is a subset of the unpaid hard words. -/
theorem bothMixedRigidWords_subset_unpaidHard
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    ascendingUnpaidRigidWords C exponent ∪
      descendingUnpaidRigidWords C exponent ⊆
        unpaidHardOverlapWords C exponent := by
  intro w hw
  rcases Finset.mem_union.mp hw with ha | hb
  · exact ascendingUnpaidRigidWords_subset_unpaidHard C exponent ha
  · exact descendingUnpaidRigidWords_subset_unpaidHard C exponent hb

/-- The TRUE final unpaid-hard words after reserving both
mixed-rigid partial credits, as an ordinary Boolean set difference. -/
noncomputable def remainingUnpaidHardAfterMixedRigidWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  unpaidHardOverlapWords C exponent \
    (ascendingUnpaidRigidWords C exponent ∪
      descendingUnpaidRigidWords C exponent)

/-- Exact cardinal split of originally unpaid hard Boolean words. -/
theorem unpaidHard_card_eq_bothMixedRigid_add_remaining
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (unpaidHardOverlapWords C exponent).card =
      (ascendingUnpaidRigidWords C exponent ∪
        descendingUnpaidRigidWords C exponent).card +
      (remainingUnpaidHardAfterMixedRigidWords C exponent).card := by
  unfold remainingUnpaidHardAfterMixedRigidWords
  have hsubset := bothMixedRigidWords_subset_unpaidHard C exponent
  rw [Finset.card_sdiff_of_subset hsubset]
  have hcard := Finset.card_le_card hsubset
  omega

/-- EXACT equivalence between earlier defect payment and the
narrower net-payment frontier after BOTH globally disjoint
mixed-rigid partial surplus reservations.

The inequality itself is not claimed unconditionally. -/
theorem completion_defect_payment_iff_after_both_mixed_rigid_credits
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
      (remainingUnpaidHardAfterMixedRigidWords C exponent).card +
      (∑ p ∈ ascendingUnpaidRigidCarriers C exponent, 2 ^ exponent p.1) +
      (∑ p ∈ descendingUnpaidRigidCarriers C exponent, 2 ^ exponent p.2) +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          (totalDyadicProfileSurplus exponent (projectedFree C) -
            (surplusPaidHardOverlapWords C exponent).card -
            (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
              dyadicProfileSurplus exponent (projectedFree C) p.1) -
            (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
              dyadicProfileSurplus exponent (projectedFree C) p.2))) := by
  have hsplit := unpaidHard_card_eq_bothMixedRigid_add_remaining
    C exponent
  have hmass := bothMixedRigidWords_card_eq_credits_add_debts
    C exponent
  have hbudget :=
    paid_hard_and_both_mixed_rigid_credits_le_total_surplus
      C exponent
  omega

#print axioms unpayable_hard_carrier_words_subset_unpaid
#print axioms ascending_descending_rigid_words_disjoint
#print axioms descendingUnpaidRigidWords_card_eq_mass
#print axioms bothMixedRigidWords_card_eq_credits_add_debts
#print axioms completion_defect_payment_iff_after_both_mixed_rigid_credits

end OrderedEdgeColoring
end JSP000404Research
