import JSP000404Research.ResidualRigidHardSurplusPacking
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Rigid-surplus-reserved residual global payment

We have now proved without an admitted lemma:
* hard words split exactly into transportable and rigid faces;
* ALL transportable hard words inject globally into singleton/soft words;
* ALL rigid faces with a strict lower projected slack and a strictly
  smaller upper free dimension have full mass payable with NO reuse of
  a lower vertex's dyadic surplus.

This module reserves the ACTUAL whole-face paid rigid words and the
exact amount of surplus they consume. It subtracts BOTH the paid
overlap-word mass and the reserved surplus, leaving an EQUIVALENT,
strictly more focused global payment inequality involving just:
  all overlap words EXCEPT the independently paid rigid ones,
  projected profile loss,
  Boolean holes,
  surplus REMAINING AFTER reserving rigid payments.

No missing payment is assumed. The reduced inequality remains OPEN:
in particular no singleton word is mistaken for a Boolean hole,
and surplus reserved here must not be charged again to soft overlaps.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Exactly the Boolean overlap words carried by rigid hard pairs
whose ENTIRE upper face has a certified one-sided lower surplus
payment. -/
noncomputable def oneSidedPaidRigidOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (oneSidedPayableRigidHardCarriers C exponent).biUnion
    (carrierOverlapWords C)

/-- Every reserved rigid word is a GENUINE globally doubly covered
word; none is an uncovered Boolean word. -/
theorem oneSidedPaidRigidOverlapWords_subset_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    oneSidedPaidRigidOverlapWords C exponent ⊆
      overlapCompletionWords C := by
  classical
  intro word hw
  obtain ⟨p,hp,hpw⟩ := Finset.mem_biUnion.mp hw
  have hpair := ((mem_oneSidedPayableRigidHardCarriers
    C exponent p).1 hp).1
  have hrig := ((mem_rigidHardOverlapCarrierPairs C p).1 hpair).1
  have hover := ((mem_hardOverlapCarrierPairs C p).1 hrig).1
  rw [overlapCompletionWords_eq_overlapCarrier_biUnion C]
  exact Finset.mem_biUnion.mpr ⟨p,hover,hpw⟩

/-- The reserved rigid Boolean words have EXACTLY the
sum of their full upper dyadic cube masses: no double count. -/
theorem oneSidedPaidRigidOverlapWords_card_eq_dyadic_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (oneSidedPaidRigidOverlapWords C exponent).card =
      ∑ p ∈ oneSidedPayableRigidHardCarriers C exponent,
        2 ^ projectedFree C p.2 := by
  classical
  have hpair :
      ((oneSidedPayableRigidHardCarriers C exponent :
          Finset (V × V)) : Set (V × V)).PairwiseDisjoint
        (carrierOverlapWords C) := by
    intro p hp q hq hpq
    apply carrierOverlapWords_pairwiseDisjoint C
    · have h0 := ((mem_oneSidedPayableRigidHardCarriers
        C exponent p).1 (by simpa using hp)).1
      have h1 := ((mem_rigidHardOverlapCarrierPairs C p).1 h0).1
      exact ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 h1).1).1
    · have h0 := ((mem_oneSidedPayableRigidHardCarriers
        C exponent q).1 (by simpa using hq)).1
      have h1 := ((mem_rigidHardOverlapCarrierPairs C q).1 h0).1
      exact ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 h1).1).1
    · exact hpq
  unfold oneSidedPaidRigidOverlapWords
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro p hp
  have h0 := ((mem_oneSidedPayableRigidHardCarriers
    C exponent p).1 hp).1
  have hrig := (mem_rigidHardOverlapCarrierPairs C p).1 h0
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hrig.1).2
  exact hard_no_transport_inter_card_eq_projected_cube
    C hsame hrig.2

/-- Proven FINITE BUDGET: every reserved overlap word is fully
backed by global profile surplus with no reused lower endpoint. -/
theorem oneSidedPaidRigidOverlapWords_card_le_totalSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (oneSidedPaidRigidOverlapWords C exponent).card ≤
      totalDyadicProfileSurplus exponent (projectedFree C) := by
  rw [oneSidedPaidRigidOverlapWords_card_eq_dyadic_sum]
  exact sum_oneSidedPayableRigidMass_le_totalSurplus C exponent

/-- The STILL-UNPAID overlap WORDS, after the independent
rigid lower-surplus payments have been committed. -/
noncomputable def afterRigidPaymentOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  overlapCompletionWords C \
    oneSidedPaidRigidOverlapWords C exponent

/-- The overlap count splits EXACTLY into paid and unpaid
parts. The two sets are disjoint by construction. -/
theorem overlap_card_eq_paidRigid_add_remaining
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (overlapCompletionWords C).card =
      (oneSidedPaidRigidOverlapWords C exponent).card +
        (afterRigidPaymentOverlapWords C exponent).card := by
  have hsubset :=
    oneSidedPaidRigidOverlapWords_subset_overlap C exponent
  unfold afterRigidPaymentOverlapWords
  rw [Finset.card_sdiff_of_subset hsubset]
  have hc := Finset.card_le_card hsubset
  omega

/-- MASTER RESIDUAL PAYMENT REDUCTION, wholly kernel-verified:
the old global inequality is EQUIVALENT to paying just the
remaining overlap words and profile losses, with the exact
one-sided rigid-surplus reservation deducted from surplus.

The reduced inequality is still the genuine, as-yet-unproved
geometric statement; this is not a proof of full JSP-000404. -/
theorem completion_defect_payment_iff_after_oneSided_rigid_reservation
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    ((overlapCompletionWords C).card +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          totalDyadicProfileSurplus exponent (projectedFree C))
    ↔
    ((afterRigidPaymentOverlapWords C exponent).card +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          (totalDyadicProfileSurplus exponent (projectedFree C) -
            (oneSidedPaidRigidOverlapWords C exponent).card)) := by
  have hmass := overlap_card_eq_paidRigid_add_remaining C exponent
  have hpaid := oneSidedPaidRigidOverlapWords_card_le_totalSurplus
    C exponent
  omega

#print axioms oneSidedPaidRigidOverlapWords_subset_overlap
#print axioms oneSidedPaidRigidOverlapWords_card_eq_dyadic_sum
#print axioms oneSidedPaidRigidOverlapWords_card_le_totalSurplus
#print axioms overlap_card_eq_paidRigid_add_remaining
#print axioms completion_defect_payment_iff_after_oneSided_rigid_reservation

end OrderedEdgeColoring
end JSP000404Research
