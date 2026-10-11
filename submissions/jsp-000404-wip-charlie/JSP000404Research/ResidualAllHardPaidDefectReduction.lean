import JSP000404Research.ResidualAllHardSurplusPacking
import JSP000404Research.ResidualRigidPaidDefectReduction
import Mathlib.Tactic

/-!
# Reserve ALL independently paid hard-overlap Boolean faces

The certified-paid class now includes EVERY hard residual carrier
whose two endpoints are projected-strict, whether transportable or
rigid, plus rigid nested faces with a strictly wider nonsaturated
lower endpoint. This strictly generalizes the previous one-sided
rigid-only reservation.

Hard carriers form a MATCHING of endpoints, so even using both
endpoint surpluses on each selected whole face entails NO reuse
of a vertex's profile-surplus capacity across selected hard pairs.

The new exact global reservation removes all selected hard overlap
Boolean words, not just their carrier labels, and deducts their exact
dyadic mass from the total surplus. The original completion-defect
payment is EQUIVALENT to paying the truly remaining overlap words
plus projected loss with only the net unreserved surplus.

No assertion is made that the remaining soft overlap, saturated
hard carriers, loss, or Boolean hole obligations are already paid.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

noncomputable def surplusPaidHardOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (surplusPayableHardCarrierPairs C exponent).biUnion
    (carrierOverlapWords C)

/-- The reserved Boolean mass belongs to hard overlap (and hence
to genuine GLOBAL double-coverage), never to Boolean holes. -/
theorem surplusPaidHardOverlapWords_subset_hard
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    surplusPaidHardOverlapWords C exponent ⊆
      hardOverlapCompletionWords C := by
  classical
  intro word hw
  obtain ⟨p,hp,hpw⟩ := Finset.mem_biUnion.mp hw
  have hhard := ((mem_surplusPayableHardCarrierPairs C exponent p).1 hp).1
  unfold hardOverlapCompletionWords
  exact Finset.mem_biUnion.mpr ⟨p,hhard,hpw⟩

theorem surplusPaidHardOverlapWords_subset_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    surplusPaidHardOverlapWords C exponent ⊆
      overlapCompletionWords C := by
  intro word hw
  have hhard := surplusPaidHardOverlapWords_subset_hard
    C exponent hw
  rw [overlapCompletionWords_eq_hard_union_soft C]
  exact Finset.mem_union.mpr (Or.inl hhard)

/-- The exact paid Boolean word mass is the sum of the WHOLE
intersection-cube masses on the selected carriers, not a sum of
individual canonical safe-flip words. -/
theorem surplusPaidHardOverlapWords_card_eq_carrier_mass
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (surplusPaidHardOverlapWords C exponent).card =
      ∑ p ∈ surplusPayableHardCarrierPairs C exponent,
        (carrierOverlapWords C p).card := by
  classical
  have hpair :
      ((surplusPayableHardCarrierPairs C exponent :
        Finset (V × V)) : Set (V × V)).PairwiseDisjoint
        (carrierOverlapWords C) := by
    intro p hp q hq hpq
    apply carrierOverlapWords_pairwiseDisjoint C
    · have h := ((mem_surplusPayableHardCarrierPairs
        C exponent p).1 (by simpa using hp)).1
      have hover := ((mem_hardOverlapCarrierPairs C p).1 h).1
      exact ((mem_overlapCarrierPairs C p).1 hover).1
    · have h := ((mem_surplusPayableHardCarrierPairs
        C exponent q).1 (by simpa using hq)).1
      have hover := ((mem_hardOverlapCarrierPairs C q).1 h).1
      exact ((mem_overlapCarrierPairs C q).1 hover).1
    · exact hpq
  unfold surplusPaidHardOverlapWords
  exact Finset.card_biUnion hpair

/-- FULL surpluses of the selected hard-pair matching pay every
reserved double-covered Boolean word. -/
theorem surplusPaidHardOverlapWords_card_le_totalSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (surplusPaidHardOverlapWords C exponent).card ≤
      totalDyadicProfileSurplus exponent (projectedFree C) := by
  rw [surplusPaidHardOverlapWords_card_eq_carrier_mass]
  exact sum_surplusPayableHardMass_le_totalSurplus C exponent

/-- The new residual overlap debt excludes ALL individually
surplus-payable hard faces. -/
noncomputable def afterAllHardPaymentOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  overlapCompletionWords C \
    surplusPaidHardOverlapWords C exponent

/-- Exact complementary decomposition into already paid hard
faces and truly remaining overlap Boolean words. -/
theorem overlap_card_eq_paidHard_add_remaining
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (overlapCompletionWords C).card =
      (surplusPaidHardOverlapWords C exponent).card +
        (afterAllHardPaymentOverlapWords C exponent).card := by
  have hsubset :=
    surplusPaidHardOverlapWords_subset_overlap C exponent
  unfold afterAllHardPaymentOverlapWords
  rw [Finset.card_sdiff_of_subset hsubset]
  have hc := Finset.card_le_card hsubset
  omega

/-- EXACTLY the same original payment as before, but now with
every fully surplus-paid hard face removed and its surplus credit
simultaneously reserved. The RHS uses NET surplus, never gross.

This is an accounting equivalence, NOT the outstanding geometric
argument required to establish either side of the equivalence. -/
theorem completion_defect_payment_iff_after_all_hard_reservation
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    ((overlapCompletionWords C).card +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          totalDyadicProfileSurplus exponent (projectedFree C))
    ↔
    ((afterAllHardPaymentOverlapWords C exponent).card +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          (totalDyadicProfileSurplus exponent (projectedFree C) -
            (surplusPaidHardOverlapWords C exponent).card)) := by
  have hmass := overlap_card_eq_paidHard_add_remaining C exponent
  have hpaid := surplusPaidHardOverlapWords_card_le_totalSurplus
    C exponent
  omega

/-- The previous one-sided rigid reservation is literally INCLUDED
in the new globally payable hard-face reservation. -/
theorem oneSidedPaidRigidOverlapWords_subset_allPaidHard
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    oneSidedPaidRigidOverlapWords C exponent ⊆
      surplusPaidHardOverlapWords C exponent := by
  classical
  intro word hw
  obtain ⟨p,hp,hpw⟩ := Finset.mem_biUnion.mp hw
  have hrigid := (oneSidedPayable_subset_twoEndpointPayable
    C exponent) hp
  have hpay := (twoEndpointPayableRigid_subset_surplusPayableHard
    C exponent) hrigid
  exact Finset.mem_biUnion.mpr ⟨p,hpay,hpw⟩

#print axioms surplusPaidHardOverlapWords_card_eq_carrier_mass
#print axioms surplusPaidHardOverlapWords_card_le_totalSurplus
#print axioms completion_defect_payment_iff_after_all_hard_reservation
#print axioms oneSidedPaidRigidOverlapWords_subset_allPaidHard

end OrderedEdgeColoring
end JSP000404Research
