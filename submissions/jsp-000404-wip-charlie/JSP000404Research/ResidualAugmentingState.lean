import JSP000404Research.ResidualSingleFibreTransition
import JSP000404Research.ResidualOverlapWitness
import Mathlib.Tactic

/-!
# Structural 0/1/2 completion states

Retained completion multiplicity is at most two.  Instead of carrying numeric
fibre cardinalities through the augmenting proof, package each Boolean word
into one of three structural states:

* uncovered;
* singly covered by a unique vertex;
* doubly covered by a unique ordered residual pair.

For a single-covered word, an active-coordinate flip either reaches an
uncovered word, another single state, or an overlap state.  In every blocked
case all new carriers activate the flipped coordinate with the opposite
canonical bit.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem completionWord_structural_trichotomy
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (word : Fin n → Bool) :
    word ∉ coveredCompletionWords C
    ∨
    (∃ v : V, IsSingleCompletionWord C v word)
    ∨
    (∃ u v : V,
      u < v ∧
      IsResidual C u v ∧
      word ∈ retainedCompletionWords C u ∧
      word ∈ retainedCompletionWords C v) := by
  classical
  have hle := completionFibre_card_le_two C word
  by_cases hzero : (completionFibre C word).card = 0
  · left
    intro hcov
    have hne :=
      (mem_coveredCompletionWords C word).1 hcov
    exact (Finset.card_pos.mpr hne).ne' hzero
  · have hpos : 0 < (completionFibre C word).card := by
      omega
    by_cases htwo : (completionFibre C word).card = 2
    · right
      right
      have hoverlap :
          word ∈ overlapCompletionWords C :=
        (mem_overlapCompletionWords C word).2 htwo
      obtain ⟨u,v,huv,hres,hu,hv,_huniq⟩ :=
        exists_ordered_residual_pair_of_overlapWord
          C hoverlap
      exact ⟨u,v,huv,hres,hu,hv⟩
    · have hone : (completionFibre C word).card = 1 := by
        omega
      right
      left
      obtain ⟨v,hfib⟩ := Finset.card_eq_one.mp hone
      refine ⟨v, ?_⟩
      constructor
      · apply (mem_completionFibre C word v).1
        rw [hfib]
        simp
      · intro w hw
        have hwF :
            w ∈ completionFibre C word :=
          (mem_completionFibre C word w).2 hw
        rw [hfib] at hwF
        simpa using hwF

theorem single_flip_structural_transition
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {owner : V} {word : Fin n → Bool} {c : Fin n}
    (hsingle : IsSingleCompletionWord C owner word)
    (hc : c ∈ retainedActive C owner) :
    let y := flipBoolWordAt word c
    y ∉ coveredCompletionWords C
    ∨
    (∃ w : V,
      IsSingleCompletionWord C w y ∧
      w ≠ owner ∧
      c ∈ retainedActive C w ∧
      retainedBit C w c = !(retainedBit C owner c))
    ∨
    (∃ u v : V,
      u < v ∧
      IsResidual C u v ∧
      y ∈ retainedCompletionWords C u ∧
      y ∈ retainedCompletionWords C v ∧
      u ≠ owner ∧ v ≠ owner ∧
      c ∈ retainedActive C u ∧
      c ∈ retainedActive C v ∧
      retainedBit C u c = !(retainedBit C owner c) ∧
      retainedBit C v c = !(retainedBit C owner c)) := by
  dsimp
  rcases completionWord_structural_trichotomy
      C (flipBoolWordAt word c)
    with hhole | hsingleNew | hoverlap
  · exact Or.inl hhole
  · right
    left
    obtain ⟨w,hwSingle⟩ := hsingleNew
    have hw := hwSingle.1
    have hne :=
      single_flip_blocker_ne_owner C hsingle hc hw
    have hactive :=
      single_flip_blocker_active C hsingle hc hw
    have hbit :=
      single_flip_blocker_bit_opposite C hsingle hc hw
    exact ⟨w,hwSingle,hne,hactive,hbit⟩
  · right
    right
    obtain ⟨u,v,huv,hres,hu,hv⟩ := hoverlap
    have huNe :=
      single_flip_blocker_ne_owner C hsingle hc hu
    have hvNe :=
      single_flip_blocker_ne_owner C hsingle hc hv
    have huActive :=
      single_flip_blocker_active C hsingle hc hu
    have hvActive :=
      single_flip_blocker_active C hsingle hc hv
    have huBit :=
      single_flip_blocker_bit_opposite C hsingle hc hu
    have hvBit :=
      single_flip_blocker_bit_opposite C hsingle hc hv
    exact ⟨u,v,huv,hres,hu,hv,
      huNe,hvNe,huActive,hvActive,huBit,hvBit⟩

#print axioms completionWord_structural_trichotomy
#print axioms single_flip_structural_transition

end OrderedEdgeColoring
end JSP000404Research
