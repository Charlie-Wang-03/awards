import JSP000404Research.ResidualAllHardPaidDefectReduction
import Mathlib.Tactic

/-!
# Exact unpaid overlap = SOFT overlap + SATURATED hard overlap

After selecting and fully paying every strictly-slack hard residual
carrier (and the extra nested one-sided payable rigid faces),
the only overlap words left are:

* ALL soft residual-overlap words, whose two canonical codes differ;
* hard overlap words whose unique hard carrier was not fully paid.

These classes are DISJOINT and their cardinalities add exactly.

The remaining hard word has an unpayable source carrier; assuming
the standard one-layer residual-active exponent budget, at least
ONE endpoint of that source carrier is PROJECTED SATURATED.

The resulting geometric gap is therefore precisely soft overlap,
saturated hard overlap, projected loss, genuine Boolean holes,
and NET unreserved profile surplus. No original payment is proved here.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Exactly the hard words whose carrier was not reserved in the
certified hard-surplus matching. -/
noncomputable def unpaidHardOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  hardOverlapCompletionWords C \
    surplusPaidHardOverlapWords C exponent

/-- The exact unpaid Boolean overlap is the DISJOINT union
of soft overlaps and the unreserved hard overlaps. -/
theorem afterAllHardPayment_eq_soft_union_unpaidHard
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    afterAllHardPaymentOverlapWords C exponent =
      softOverlapCompletionWords C ∪
        unpaidHardOverlapWords C exponent := by
  classical
  unfold afterAllHardPaymentOverlapWords unpaidHardOverlapWords
  rw [overlapCompletionWords_eq_hard_union_soft C]
  ext word
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hh | hs, hnot⟩
    · exact Or.inr ⟨hh,hnot⟩
    · exact Or.inl hs
  · rintro (hs | ⟨hh,hnot⟩)
    · constructor
      · exact Or.inr hs
      · intro hpaid
        have hhard := surplusPaidHardOverlapWords_subset_hard
          C exponent hpaid
        exact (Finset.disjoint_left.mp
          (hard_soft_overlap_words_disjoint C)) hhard hs
    · exact ⟨Or.inl hh,hnot⟩

/-- No soft-overlap word can be an unreserved hard-overlap
word, regardless of exponent profile. -/
theorem soft_unpaidHardOverlap_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (softOverlapCompletionWords C)
      (unpaidHardOverlapWords C exponent) := by
  apply Finset.disjoint_left.mpr
  intro word hs hu
  have hhard :
      word ∈ hardOverlapCompletionWords C :=
    (Finset.mem_sdiff.mp hu).1
  exact (Finset.disjoint_left.mp
    (hard_soft_overlap_words_disjoint C)) hhard hs

/-- Exact restricted overlap count, without ever miscounting
soft and hard residual intersections as the same Boolean word. -/
theorem afterAllHardPayment_card_eq_soft_add_unpaidHard
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (afterAllHardPaymentOverlapWords C exponent).card =
      (softOverlapCompletionWords C).card +
        (unpaidHardOverlapWords C exponent).card := by
  rw [afterAllHardPayment_eq_soft_union_unpaidHard C exponent]
  exact Finset.card_union_of_disjoint
    (soft_unpaidHardOverlap_disjoint C exponent)

/-- An unpaid hard word is carried by a UNIQUE hard residual
pair that is absent from the independent surplus-paid matching. -/
theorem unpaidHardWord_has_unpayable_hard_carrier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {word : Fin n → Bool}
    (hunpaid : word ∈ unpaidHardOverlapWords C exponent) :
    ∃ p : V × V,
      p ∈ hardOverlapCarrierPairs C ∧
      p ∉ surplusPayableHardCarrierPairs C exponent ∧
      word ∈ carrierOverlapWords C p := by
  classical
  have hparts := Finset.mem_sdiff.mp hunpaid
  let x : {w : Fin n → Bool // w ∈ hardOverlapCompletionWords C} :=
    ⟨word,hparts.1⟩
  let p := hardWordCarrier C x
  have hcarrier : p.1 ∈ hardOverlapCarrierPairs C := p.2
  have hword : word ∈ carrierOverlapWords C p.1 :=
    hardWordCarrier_covers C x
  have hnot : p.1 ∉ surplusPayableHardCarrierPairs C exponent := by
    intro hpay
    exact hparts.2 (Finset.mem_biUnion.mpr
      ⟨p.1,hpay,hword⟩)
  exact ⟨p.1,hcarrier,hnot,hword⟩

/-- Under the genuine ONE-LAYER residual-active profile budget,
every unpaid hard word is carried by a hard residual pair with
AT LEAST ONE SATURATED ENDPOINT.

This is substantially sharper than the old entire-hard-overlap
obligation, but it does not pay saturated hard overlaps. -/
theorem unpaidHardWord_has_saturated_endpoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {word : Fin n → Bool}
    (hunpaid : word ∈ unpaidHardOverlapWords C exponent) :
    ∃ p : V × V,
      p ∈ hardOverlapCarrierPairs C ∧
      word ∈ carrierOverlapWords C p ∧
      (exponent p.1 = projectedFree C p.1 ∨
       exponent p.2 = projectedFree C p.2) := by
  obtain ⟨p,hcarrier,hnot,hword⟩ :=
    unpaidHardWord_has_unpayable_hard_carrier C exponent hunpaid
  have hboth := (mem_carrierOverlapWords C p word).1 hword
  have hoverlap : word ∈ overlapCompletionWords C := by
    rw [overlapCompletionWords_eq_hard_union_soft C]
    have hh : word ∈ hardOverlapCompletionWords C := by
      unfold hardOverlapCompletionWords
      exact Finset.mem_biUnion.mpr ⟨p,hcarrier,hword⟩
    exact Finset.mem_union.mpr (Or.inl hh)
  have hresLo := residual_mem_active_of_overlapWord_member
    C hoverlap hboth.1
  have hresHi := residual_mem_active_of_overlapWord_member
    C hoverlap hboth.2
  have hbudgetLo := exponent_le_projectedFree_of_residual_mem
    C exponent hexp honeLoss hresLo
  have hbudgetHi := exponent_le_projectedFree_of_residual_mem
    C exponent hexp honeLoss hresHi
  have hsat := hard_not_payable_implies_endpoint_saturation
    C exponent hcarrier hbudgetLo hbudgetHi hnot
  exact ⟨p,hcarrier,hword,hsat⟩

/-- Reformulate the still-open global defect payment as the
EXACT narrower SOFT + UNPAID HARD (hence saturated under the
one-layer budget) + projected-loss balance. -/
theorem completion_defect_payment_iff_soft_and_unpaid_hard
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    ((overlapCompletionWords C).card +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          totalDyadicProfileSurplus exponent (projectedFree C))
    ↔
    ((softOverlapCompletionWords C).card +
      (unpaidHardOverlapWords C exponent).card +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          (totalDyadicProfileSurplus exponent (projectedFree C) -
            (surplusPaidHardOverlapWords C exponent).card)) := by
  rw [completion_defect_payment_iff_after_all_hard_reservation]
  rw [afterAllHardPayment_card_eq_soft_add_unpaidHard]

#print axioms afterAllHardPayment_eq_soft_union_unpaidHard
#print axioms afterAllHardPayment_card_eq_soft_add_unpaidHard
#print axioms unpaidHardWord_has_saturated_endpoint
#print axioms completion_defect_payment_iff_soft_and_unpaid_hard

end OrderedEdgeColoring
end JSP000404Research
