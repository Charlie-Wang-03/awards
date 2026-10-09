import JSP000404Research.DirectionDataThreePointG1Audit
import JSP000404Research.FullDyadicInternalResidualExactBoundaryInterface
import Mathlib.Tactic

/-!
# Auditing the G1 geometric exclusion against the 3-point DirectionData model

This module isolates the finite Boolean-block calculation for the explicit
three-point DirectionData with cyclic exponents (1,0,0).

If the two high-band endpoints share one retained cube of cardinality two,
their combined demands 2+1 exceed that block cardinality. This is a genuine
loss-free Hall-deficient pair, falsifying the blanket G1 exact-boundary
exclusion for this level of abstraction.

No claim about an actual planar point realization is made here. The
DirectionData axioms and explicit LocalDirectionCycle values are proved in
the imported audit file.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

private noncomputable def exampleB : OrderedEdgeColoring (Fin 3) 3 :=
  standardResidualColoring candidateThreePointData 2 (by norm_num)

private noncomputable def exampleK (i : Fin 3) : ℕ :=
  (candidateThreeCycles i).exponent

theorem exampleK_at_zero : exampleK 0 = 1 :=
  candidateThreePoint_cycles_exponents.1

theorem exampleK_at_one : exampleK 1 = 0 :=
  candidateThreePoint_cycles_exponents.2.1

theorem exampleB_residual_zero_one :
    IsResidual exampleB 0 1 := by
  have hval : candidateThreePointData.value 0 1 =
      ((21 : ℝ) / 10) := by rfl
  apply (standardResidual_iff_high
    candidateThreePointData 2 (by norm_num)
    (by decide)).2
  rw [hval]
  norm_num

/-- Both endpoints have no incoming retained-colour edge. -/
private theorem exampleB_retained_active_pair :
    retainedActive exampleB 0 = ({(1 : Fin 2)} : Finset (Fin 2)) ∧
    retainedActive exampleB 1 = ({(1 : Fin 2)} : Finset (Fin 2)) := by
  simpa only [exampleB] using candidateThreePoint_retainedActive_01

theorem exampleB_retained_bits_both_false (c : Fin 2) :
    retainedBit exampleB 0 c = false ∧
    retainedBit exampleB 1 c = false := by
  constructor
  · change bit exampleB 0 c.castSucc = false
    apply (bit_eq_false_iff exampleB 0 c.castSucc).2
    rintro ⟨w, hw, _⟩
    exact (Fin.not_lt_zero w) hw
  · change bit exampleB 1 c.castSucc = false
    apply (bit_eq_false_iff exampleB 1 c.castSucc).2
    rintro ⟨w, hw, hcol⟩
    have hw0 : w = (0 : Fin 3) := by
      omega
    subst w
    have hvalEq := congrArg Fin.val hcol
    have hcLt : c.castSucc.val < 2 := c.isLt
    exact exampleB_residual_zero_one (by omega)

/-- The two endpoints impose the same retained partial code. -/
theorem exampleB_same_retained_completion_block :
    retainedCompletionWords exampleB 0 =
      retainedCompletionWords exampleB 1 := by
  have hp := exampleB_retained_active_pair
  ext word
  constructor
  · intro hw
    apply (mem_retainedCompletionWords exampleB 1 word).2
    intro c hc1
    have hc0 : c ∈ retainedActive exampleB 0 := by
      simpa [hp.1, hp.2] using hc1
    have heq :=
      (mem_retainedCompletionWords exampleB 0 word).1 hw c hc0
    simpa [((exampleB_retained_bits_both_false c).1),
      ((exampleB_retained_bits_both_false c).2)] using heq
  · intro hw
    apply (mem_retainedCompletionWords exampleB 0 word).2
    intro c hc0
    have hc1 : c ∈ retainedActive exampleB 1 := by
      simpa [hp.1, hp.2] using hc0
    have heq :=
      (mem_retainedCompletionWords exampleB 1 word).1 hw c hc1
    simpa [((exampleB_retained_bits_both_false c).1),
      ((exampleB_retained_bits_both_false c).2)] using heq

theorem exampleB_zero_completion_card :
    (retainedCompletionWords exampleB 0).card = 2 := by
  rw [retainedCompletionWords_card]
  have hpal := exampleB_retained_active_pair.1
  rw [hpal]
  norm_num

theorem exampleB_projectedFree_01 :
    projectedFree exampleB 0 = 1 ∧
    projectedFree exampleB 1 = 1 := by
  have hp := exampleB_retained_active_pair
  simp [projectedFree, hp.1, hp.2]

theorem exampleB_zero_one_nonloss :
    (0 : Fin 3) ∉ projectedLossVertices exampleB exampleK ∧
    (1 : Fin 3) ∉ projectedLossVertices exampleB exampleK := by
  have hf := exampleB_projectedFree_01
  constructor
  · intro h
    have heq := (mem_projectedLossVertices exampleB exampleK 0).1 h
    rw [exampleK_at_zero, hf.1] at heq
    omega
  · intro h
    have heq := (mem_projectedLossVertices exampleB exampleK 1).1 h
    rw [exampleK_at_one, hf.2] at heq
    omega

/-- A genuine loss-free two-vertex Hall obstruction in the candidate
3-point DirectionData. This refutes G1 at the abstract model level
once the concrete Boolean equalities above have been verified by Lean. -/
theorem candidateThreePoint_has_loss_free_deficient_pair :
    ∃ T : Finset (Fin 3),
      BlockDeficient (fun i => 2 ^ exampleK i)
        (enlargedProjectedCandidateBlock exampleB exampleK) T ∧
      ∀ v ∈ T, v ∉ projectedLossVertices exampleB exampleK := by
  classical
  let T : Finset (Fin 3) := {0, 1}
  have hn0 := exampleB_zero_one_nonloss.1
  have hn1 := exampleB_zero_one_nonloss.2
  have hb0 :=
    enlargedProjectedCandidateBlock_nonloss exampleB exampleK hn0
  have hb1 :=
    enlargedProjectedCandidateBlock_nonloss exampleB exampleK hn1
  have hQ := exampleB_same_retained_completion_block
  have hUnion :
      T.biUnion (enlargedProjectedCandidateBlock exampleB exampleK) =
        retainedCompletionWords exampleB 0 := by
    simp [T, hb0, hb1, ← hQ]
  have hDemand : (∑ i ∈ T, 2 ^ exampleK i) = 3 := by
    simp [T, exampleK_at_zero, exampleK_at_one]
  refine ⟨T, ?_, ?_⟩
  · unfold BlockDeficient
    rw [hUnion, exampleB_zero_completion_card, hDemand]
    norm_num
  · intro v hv
    simp [T] at hv
    rcases hv with rfl | rfl
    · exact hn0
    · exact hn1

#print axioms candidateThreePoint_has_loss_free_deficient_pair

/-- Genuine abstract DirectionData contradicts the *universally*
quantified G1-exclusion predicate. This does NOT refute the target
dyadic bound, nor establish realizability by a planar point set. -/
theorem candidateThreePoint_refutes_abstract_G1 :
    ¬ LossFreeMinimalHallInternalResidualExactExcluded exampleB exampleK := by
  classical
  intro hG1
  obtain ⟨T, hdef, hnoLoss⟩ :=
    candidateThreePoint_has_loss_free_deficient_pair
  obtain ⟨U, hUT, hUdef, hUmin⟩ :=
    exists_minimal_deficient_subset
      (fun i : Fin 3 => 2 ^ exampleK i)
      (enlargedProjectedCandidateBlock exampleB exampleK)
      hdef
  have hnoLossU :
      ∀ v ∈ U, v ∉ projectedLossVertices exampleB exampleK := by
    intro v hv
    exact hnoLoss v (hUT hv)
  obtain ⟨v, hvU, _hvNoLoss, hvExact⟩ :=
    deficient_loss_free_core_has_exact_nonloss
      candidateThreePointData (by norm_num) candidateThreeCycles
      hUdef hnoLossU
  have hNeighbor :=
    minimal_loss_free_deficient_core_has_internal_residual_neighbor
      candidateThreePointData (by norm_num) candidateThreeCycles
      hUdef hUmin hnoLossU v hvU
  exact (hG1 U hUdef hUmin hnoLossU v hvU hNeighbor) hvExact

#print axioms candidateThreePoint_refutes_abstract_G1

/-- Even the original broad G1 assertion (every minimal Hall core
has a projected-loss centre) is false for genuine abstract DirectionData. -/
theorem candidateThreePoint_refutes_broad_G1 :
    ¬ EveryMinimalHallCoreHasProjectedLoss exampleB exampleK := by
  classical
  intro hBroad
  obtain ⟨T, hdef, hnoLoss⟩ :=
    candidateThreePoint_has_loss_free_deficient_pair
  obtain ⟨U, hUT, hUdef, hUmin⟩ :=
    exists_minimal_deficient_subset
      (fun i : Fin 3 => 2 ^ exampleK i)
      (enlargedProjectedCandidateBlock exampleB exampleK)
      hdef
  obtain ⟨v, hvU, hvLoss⟩ := hBroad U hUdef hUmin
  exact hnoLoss v (hUT hvU) hvLoss

/-- Hence the intermediate exact-boundary G1 interface is also false on
the DirectionData-only abstraction. -/
theorem candidateThreePoint_refutes_exact_G1 :
    ¬ LossFreeMinimalHallExactBoundaryExcluded exampleB exampleK := by
  intro hExact
  have hBroad :=
    minimal_hall_core_has_loss_of_exact_boundary_exclusion
      candidateThreePointData (by norm_num) candidateThreeCycles hExact
  exact candidateThreePoint_refutes_broad_G1 hBroad

/-- Failure of candidate-block Hall expansion does NOT imply failure of
the desired dyadic capacity. This example is an exact-equality case. -/
theorem candidateThreePoint_total_dyadic_eq :
    (∑ i : Fin 3, 2 ^ exampleK i) = 2 ^ (2 : ℕ) := by
  have h2 : exampleK 2 = 0 :=
    candidateThreePoint_cycles_exponents.2.2
  simp [Fin.sum_univ_succ, exampleK_at_zero,
    exampleK_at_one, h2]

#print axioms candidateThreePoint_refutes_broad_G1
#print axioms candidateThreePoint_refutes_exact_G1
#print axioms candidateThreePoint_total_dyadic_eq



/-- Regression certificate for the replacement architecture: the example
has subset-Hall deficiency but exactly BALANCES global completion payment.
No local Hall-expansion assumption is used. -/
theorem candidateThreePoint_global_payment_exact :
    (overlapCompletionWords exampleB).card +
        totalDyadicProfileLoss exampleK (projectedFree exampleB) =
      (2 ^ (2 : ℕ) - (coveredCompletionWords exampleB).card) +
        totalDyadicProfileSurplus exampleK (projectedFree exampleB) := by
  have haccount :=
    residual_projection_accounting_balance
      exampleK (projectedFree exampleB)
      (coveredCompletionWords exampleB).card
      (overlapCompletionWords exampleB).card
      (projectedFree_mass_eq_covered_add_overlap exampleB)
  have hcover :
      (coveredCompletionWords exampleB).card ≤ 2 ^ (2 : ℕ) :=
    coveredCompletionWords_card_le_two_pow exampleB
  have htarget := candidateThreePoint_total_dyadic_eq
  omega

/-- The concrete failure of the *subset* Hall-G1 condition coexists
with exact success of the *global* completion-payment identity. -/
theorem candidateThreePoint_refutes_G1_but_pays_globally :
    (¬ LossFreeMinimalHallInternalResidualExactExcluded exampleB exampleK) ∧
    (overlapCompletionWords exampleB).card +
        totalDyadicProfileLoss exampleK (projectedFree exampleB) =
      (2 ^ (2 : ℕ) - (coveredCompletionWords exampleB).card) +
        totalDyadicProfileSurplus exampleK (projectedFree exampleB) :=
  ⟨candidateThreePoint_refutes_abstract_G1,
    candidateThreePoint_global_payment_exact⟩

#print axioms candidateThreePoint_global_payment_exact
#print axioms candidateThreePoint_refutes_G1_but_pays_globally

end DirectionData
end JSP000404Research
