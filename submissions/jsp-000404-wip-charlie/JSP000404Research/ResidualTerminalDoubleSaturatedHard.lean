import JSP000404Research.ResidualBothMixedRigidNetReduction
import JSP000404Research.ResidualUnpaidHardTerminalClassification
import Mathlib.Tactic

/-!
# Final hard carrier type after BOTH symmetric mixed-rigid credits

Assume the standard residual-active one-layer budget. The complete
Boolean hard-overlap words still unpaid after both independently
reserved partial credits have exactly two possible carrier types:

  (1) outgoing/inactive-coordinate TRANSPORTABLE hard carrier;
  (2) RIGID hard carrier with BOTH endpoints projected-saturated.

This is a genuine sharpening of the prior "transportable OR lower
saturated" dichotomy. The mixed rigid classes with either strict
endpoint are now fully accounted for by certified surplus credit plus
one strict-endpoint target weight.

No Boolean holes are produced by this classification alone, and
no global planar defect payment is claimed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A rigid carrier belonging to the remaining hard Boolean set
has BOTH endpoints exactly saturated, not just its lower one. -/
theorem remaining_rigid_hard_word_both_endpoints_saturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {word : Fin n → Bool} {p : V × V}
    (hword :
      word ∈ remainingUnpaidHardAfterMixedRigidWords C exponent)
    (hrigid : p ∈ rigidHardOverlapCarrierPairs C)
    (hpw : word ∈ carrierOverlapWords C p) :
    exponent p.1 = projectedFree C p.1 ∧
      exponent p.2 = projectedFree C p.2 := by
  classical
  have hparts := (Finset.mem_sdiff.mp hword)
  have hunpaid : word ∈ unpaidHardOverlapWords C exponent := hparts.1
  have hnotUnion := hparts.2
  have hnotA : word ∉ ascendingUnpaidRigidWords C exponent := by
    intro hwA
    exact hnotUnion (Finset.mem_union.mpr (Or.inl hwA))
  have hwordA :
      word ∈ unpaidHardOverlapWords C exponent \
        ascendingUnpaidRigidWords C exponent :=
    Finset.mem_sdiff.mpr ⟨hunpaid,hnotA⟩
  have hsatLo :=
    remaining_unpaid_rigid_word_has_saturated_lower
      C exponent hexp honeLoss hwordA hrigid hpw
  have hhard : p ∈ hardOverlapCarrierPairs C :=
    ((mem_rigidHardOverlapCarrierPairs C p).1 hrigid).1
  have hwordHard : word ∈ hardOverlapCompletionWords C := by
    unfold hardOverlapCompletionWords
    exact Finset.mem_biUnion.mpr ⟨p, hhard, hpw⟩
  have hoverlap : word ∈ overlapCompletionWords C := by
    rw [overlapCompletionWords_eq_hard_union_soft C]
    exact Finset.mem_union.mpr (Or.inl hwordHard)
  have hboth := (mem_carrierOverlapWords C p word).1 hpw
  have hresHi :=
    residual_mem_active_of_overlapWord_member
      C hoverlap hboth.2
  have hbudgetHi :=
    exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss hresHi
  have hnotPaid : p ∉ surplusPayableHardCarrierPairs C exponent := by
    intro hpaid
    have hwPaid : word ∈ surplusPaidHardOverlapWords C exponent :=
      Finset.mem_biUnion.mpr ⟨p,hpaid,hpw⟩
    exact (Finset.mem_sdiff.mp hunpaid).2 hwPaid
  have hsatHi : exponent p.2 = projectedFree C p.2 := by
    by_contra hneq
    have hstrictHi : exponent p.2 < projectedFree C p.2 := by omega
    have hpB : p ∈ descendingUnpaidRigidCarriers C exponent :=
      (mem_descendingUnpaidRigidCarriers C exponent p).2
        ⟨hrigid,hnotPaid,hsatLo,hstrictHi⟩
    have hwB : word ∈ descendingUnpaidRigidWords C exponent :=
      Finset.mem_biUnion.mpr ⟨p,hpB,hpw⟩
    exact hnotUnion (Finset.mem_union.mpr (Or.inr hwB))
  exact ⟨hsatLo,hsatHi⟩

/-- After paying both mixed rigid orientations, a remaining
unpaid hard word is carried EITHER by a transportable hard edge
OR by a rigid edge with BOTH projected profiles saturated. -/
theorem remaining_hard_word_transport_or_doubly_saturated_rigid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {word : Fin n → Bool}
    (hword :
      word ∈ remainingUnpaidHardAfterMixedRigidWords C exponent) :
    ∃ p : V × V,
      p ∈ hardOverlapCarrierPairs C ∧
      word ∈ carrierOverlapWords C p ∧
      (HasOutgoingHardTransport C p.1 p.2 ∨
       (p ∈ rigidHardOverlapCarrierPairs C ∧
        exponent p.1 = projectedFree C p.1 ∧
        exponent p.2 = projectedFree C p.2)) := by
  classical
  have hunpaid : word ∈ unpaidHardOverlapWords C exponent :=
    (Finset.mem_sdiff.mp hword).1
  obtain ⟨p,hhard,_hnot,hpw⟩ :=
    unpaidHardWord_has_unpayable_hard_carrier C exponent hunpaid
  refine ⟨p,hhard,hpw,?_⟩
  by_cases hr : p ∈ rigidHardOverlapCarrierPairs C
  · right
    obtain ⟨hlo,hhi⟩ :=
      remaining_rigid_hard_word_both_endpoints_saturated
        C exponent hexp honeLoss hword hr hpw
    exact ⟨hr,hlo,hhi⟩
  · left
    by_contra htransport
    exact hr ((mem_rigidHardOverlapCarrierPairs C p).2
      ⟨hhard,htransport⟩)

#print axioms remaining_rigid_hard_word_both_endpoints_saturated
#print axioms remaining_hard_word_transport_or_doubly_saturated_rigid

end OrderedEdgeColoring
end JSP000404Research
