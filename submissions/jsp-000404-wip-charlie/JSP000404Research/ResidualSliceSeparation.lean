
import JSP000404Research.ResidualLossWords
import Mathlib.Tactic

/-!
# Residual-inactive cubes are isolated; overlaps split into two residual slices

The residual projection has a sharper structure than mere multiplicity two.

1. If the residual colour is inactive at v, then the retained completion cube
   Q_v is disjoint from every Q_w with w != v.  Any nontrivial projected
   overlap would force vw to be a residual edge, making the residual colour
   active at v.

2. Therefore every overlap word is carried only by residual-active vertices.

3. On residual-active vertices the canonical bit at the residual coordinate
   splits the projected cubes into two families.  Cubes in the same residual
   bit slice are pairwise disjoint: if two such cubes overlapped, their joining
   edge would be residual, whose own colour bit is necessarily different at
   the two endpoints.

Thus all projected overlap occurs only across the two canonical residual-bit
slices.  This cleanly separates the overlap cost from the profile-loss cost.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Residual inactivity alone, with no exponent hypothesis, isolates the whole
retained completion cube. -/
theorem residualInactive_completion_disjoint
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V}
    (hinactive : residualCoord n ∉ active C v)
    (hvw : v ≠ w) :
    Disjoint
      (retainedCompletionWords C v)
      (retainedCompletionWords C w) := by
  classical
  rw [Finset.disjoint_left]
  intro word hvWord hwWord
  rcases retainedCompletion_overlap_forces_residual
      C hvw hvWord hwWord with hres | hres
  · exact hinactive
      (residualCoord_mem_active_of_isResidual
        C hres.1 hres.2).1
  · exact hinactive
      (residualCoord_mem_active_of_isResidual
        C hres.1 hres.2).2

/-- Any endpoint carrying an overlap word is residual-active. -/
theorem residual_mem_active_of_overlapWord_member
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {word : Fin n → Bool}
    (hoverlap : word ∈ overlapCompletionWords C)
    {v : V}
    (hvWord : word ∈ retainedCompletionWords C v) :
    residualCoord n ∈ active C v := by
  obtain ⟨u, w, huw, hres, huWord, hwWord, huniq⟩ :=
    exists_ordered_residual_pair_of_overlapWord C hoverlap
  rcases huniq v hvWord with rfl | rfl
  · exact
      (residualCoord_mem_active_of_isResidual
        C huw hres).1
  · exact
      (residualCoord_mem_active_of_isResidual
        C huw hres).2

/-- Under the one-layer active bound, every residual-active vertex already
satisfies the exact retained projected budget. -/
theorem exponent_le_projectedFree_of_residual_mem
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v : V}
    (hres : residualCoord n ∈ active C v) :
    exponent v ≤ projectedFree C v := by
  have hret :
      (retainedActive C v).card ≤
        n - exponent v :=
    retainedActive_card_le_of_active_le_add_one_of_residual_mem
      C v (honeLoss v) hres
  have hk := hexp v
  unfold projectedFree
  omega

/-- Hence an overlap endpoint can never be an exact projected-loss vertex. -/
theorem overlapWord_member_not_projectedLoss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {word : Fin n → Bool}
    (hoverlap : word ∈ overlapCompletionWords C)
    {v : V}
    (hvWord : word ∈ retainedCompletionWords C v) :
    v ∉ projectedLossVertices C exponent := by
  intro hvLoss
  have hle :=
    exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss
      (residual_mem_active_of_overlapWord_member
        C hoverlap hvWord)
  have heq :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  omega

/-- Residual-active vertices in one canonical residual-bit slice. -/
noncomputable def residualActiveSlice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b : Bool) : Finset V := by
  classical
  exact Finset.univ.filter fun v =>
    residualCoord n ∈ active C v ∧
    bit C v (residualCoord n) = b

@[simp] theorem mem_residualActiveSlice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b : Bool) (v : V) :
    v ∈ residualActiveSlice C b ↔
      residualCoord n ∈ active C v ∧
      bit C v (residualCoord n) = b := by
  classical
  simp [residualActiveSlice]

/-- Cubes inside one canonical residual-bit slice are pairwise disjoint. -/
theorem residualActiveSlice_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b : Bool) :
    ((residualActiveSlice C b : Finset V) : Set V).PairwiseDisjoint
      (retainedCompletionWords C) := by
  intro u hu v hv huv
  classical
  rw [Finset.disjoint_left]
  intro word huWord hvWord
  rcases retainedCompletion_overlap_forces_residual
      C huv huWord hvWord with hres | hres
  · have hbitNe :
        bit C u (residualCoord n) ≠
          bit C v (residualCoord n) := by
      have hcol :
          C.color u v = residualCoord n := by
        apply Fin.ext
        simpa [residualCoord] using residual_val_eq C hres.2
      have hne := edgeColor_bit_ne C hres.1
      simpa [hcol] using hne
    have huBit := (mem_residualActiveSlice C b u).1 hu |>.2
    have hvBit := (mem_residualActiveSlice C b v).1 hv |>.2
    exact hbitNe (huBit.trans hvBit.symm)
  · have hbitNe :
        bit C v (residualCoord n) ≠
          bit C u (residualCoord n) := by
      have hcol :
          C.color v u = residualCoord n := by
        apply Fin.ext
        simpa [residualCoord] using residual_val_eq C hres.2
      have hne := edgeColor_bit_ne C hres.1
      simpa [hcol] using hne
    have huBit := (mem_residualActiveSlice C b u).1 hu |>.2
    have hvBit := (mem_residualActiveSlice C b v).1 hv |>.2
    exact hbitNe (hvBit.trans huBit.symm)

/-- Every overlap word is shared across opposite canonical residual-bit
slices. -/
theorem overlapWord_has_opposite_residual_bits
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {word : Fin n → Bool}
    (hoverlap : word ∈ overlapCompletionWords C) :
    ∃ u v : V,
      u < v ∧
      word ∈ retainedCompletionWords C u ∧
      word ∈ retainedCompletionWords C v ∧
      bit C u (residualCoord n) = false ∧
      bit C v (residualCoord n) = true := by
  obtain ⟨u, v, huv, hres, huWord, hvWord, _⟩ :=
    exists_ordered_residual_pair_of_overlapWord C hoverlap
  have hcol :
      C.color u v = residualCoord n := by
    apply Fin.ext
    simpa [residualCoord] using residual_val_eq C hres
  have huFalse := edgeColor_bit_lower_eq_false C huv
  have hvTrue := edgeColor_bit_upper_eq_true C huv
  rw [hcol] at huFalse hvTrue
  exact ⟨u, v, huv, huWord, hvWord, huFalse, hvTrue⟩

#print axioms residualInactive_completion_disjoint
#print axioms residual_mem_active_of_overlapWord_member
#print axioms exponent_le_projectedFree_of_residual_mem
#print axioms residualActiveSlice_pairwiseDisjoint
#print axioms overlapWord_has_opposite_residual_bits

end OrderedEdgeColoring
end JSP000404Research
