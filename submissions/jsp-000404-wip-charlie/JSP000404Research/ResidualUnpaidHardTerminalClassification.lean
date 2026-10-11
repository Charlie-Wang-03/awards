import JSP000404Research.ResidualUnpaidRigidNetPaymentReduction
import Mathlib.Tactic

/-!
# Remaining hard-word terminal classification after partial rigid payments

After the new ascending-rigid partial surplus reservation, a genuinely
unpaid hard Boolean word has one of two carrier mechanisms:

  (1) the carrier admits an outgoing/inactive retained flip, or
  (2) the carrier is rigid and its LOWER endpoint is projected-saturated.

In particular there are NO unaccounted rigid carriers with strictly
slack lower endpoints: their entire Boolean face was split into a
certified global partial credit and an exact lower target-weight debt.

These statements use only the ordinary one-layer residual-active
profile budget, not a new global planar Hall hypothesis. The
transportable class and saturated-lower rigid class are not
asserted to be globally hole-paid.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A remaining unpaid RIGID word must have its carrier's
LOWER endpoint exactly projected-budget saturated. All
strict-lower rigid carriers were already handled by the
certified partial credit plus lower target-weight decomposition. -/
theorem remaining_unpaid_rigid_word_has_saturated_lower
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {word : Fin n → Bool} {p : V × V}
    (hword :
      word ∈ unpaidHardOverlapWords C exponent \
        ascendingUnpaidRigidWords C exponent)
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hpw : word ∈ carrierOverlapWords C p) :
    exponent p.1 = projectedFree C p.1 := by
  classical
  have hboth := (mem_carrierOverlapWords C p word).1 hpw
  have hhard : p ∈ hardOverlapCarrierPairs C :=
    ((mem_rigidHardOverlapCarrierPairs C p).1 hrigid).1
  have hoverlap : word ∈ overlapCompletionWords C := by
    rw [overlapCompletionWords_eq_hard_union_soft C]
    apply Finset.mem_union.mpr
    left
    unfold hardOverlapCompletionWords
    exact Finset.mem_biUnion.mpr ⟨p, hhard, hpw⟩
  have hresLo :=
    residual_mem_active_of_overlapWord_member
      C hoverlap hboth.1
  have hresHi :=
    residual_mem_active_of_overlapWord_member
      C hoverlap hboth.2
  have hbudgetLo :=
    exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss hresLo
  have hbudgetHi :=
    exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss hresHi
  have hunpaid :
      word ∈ unpaidHardOverlapWords C exponent :=
    (Finset.mem_sdiff.mp hword).1
  have hnotPaid :
      p ∉ surplusPayableHardCarrierPairs C exponent := by
    intro hpay
    have hpaidWord :
        word ∈ surplusPaidHardOverlapWords C exponent :=
      Finset.mem_biUnion.mpr ⟨p, hpay, hpw⟩
    exact (Finset.mem_sdiff.mp hunpaid).2 hpaidWord
  by_cases hlo : exponent p.1 < projectedFree C p.1
  · have ha :
        p ∈ ascendingUnpaidRigidCarriers C exponent :=
      (mem_ascendingUnpaidRigidCarriers C exponent p).2
        ⟨hrigid, hnotPaid, hlo, hbudgetHi⟩
    have hwAsc :
        word ∈ ascendingUnpaidRigidWords C exponent :=
      Finset.mem_biUnion.mpr ⟨p, ha, hpw⟩
    exact False.elim ((Finset.mem_sdiff.mp hword).2 hwAsc)
  · omega

/-- Every still unpaid hard Boolean word is owned either by an
OUTGOING-TRANSPORTABLE hard carrier or by a carrier whose LOWER
endpoint is projected saturated. This is the sharpened terminal
dichotomy after globally reserving ascending-rigid partial credit. -/
theorem remaining_unpaid_hard_word_transport_or_lower_saturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {word : Fin n → Bool}
    (hword :
      word ∈ unpaidHardOverlapWords C exponent \
        ascendingUnpaidRigidWords C exponent) :
    ∃ p : V × V,
      p ∈ hardOverlapCarrierPairs C ∧
      word ∈ carrierOverlapWords C p ∧
      (HasOutgoingHardTransport C p.1 p.2 ∨
        exponent p.1 = projectedFree C p.1) := by
  classical
  have hunpaid :
      word ∈ unpaidHardOverlapWords C exponent :=
    (Finset.mem_sdiff.mp hword).1
  obtain ⟨p, hhard, hnot, hpw⟩ :=
    unpaidHardWord_has_unpayable_hard_carrier C exponent hunpaid
  refine ⟨p, hhard, hpw, ?_⟩
  by_cases hrigid : p ∈ rigidHardOverlapCarrierPairs C
  · right
    exact remaining_unpaid_rigid_word_has_saturated_lower
      C exponent hexp honeLoss hword hrigid hpw
  · left
    by_contra hno
    exact hrigid
      ((mem_rigidHardOverlapCarrierPairs C p).2 ⟨hhard, hno⟩)

#print axioms remaining_unpaid_rigid_word_has_saturated_lower
#print axioms remaining_unpaid_hard_word_transport_or_lower_saturated

end OrderedEdgeColoring
end JSP000404Research
