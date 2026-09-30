import JSP000404Research.ResidualCompletionMultiplicity
import Mathlib.Tactic

/-!
# Unique blocker once a displaced word keeps one known carrier

The global augmenting argument should use displacements that keep the target
word inside one known completion cube while removing it from the other old
endpoint. Completion multiplicity is at most two. Therefore, after fixing the
known surviving carrier, there is at most one additional blocking vertex.

This is the deterministic-successor interface needed for a functional
augmenting graph. It applies directly to

* unsafe lower-inactive flips, which stay in the lower cube and leave the
  upper cube;
* safe active-only flips, which stay in exactly one endpoint cube.

No geometry is used here.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem additional_completion_blocker_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {anchor w₁ w₂ : V}
    {word : Fin n → Bool}
    (hanchor : word ∈ retainedCompletionWords C anchor)
    (hw₁ : word ∈ retainedCompletionWords C w₁)
    (hw₂ : word ∈ retainedCompletionWords C w₂)
    (hw₁ne : w₁ ≠ anchor)
    (hw₂ne : w₂ ≠ anchor) :
    w₁ = w₂ := by
  by_contra hne
  exact no_three_distinct_share_retained_completion
    C hw₁ne.symm hw₂ne.symm hne
    hanchor hw₁ hw₂

theorem exists_unique_additional_blocker_of_not_single
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {anchor : V}
    {word : Fin n → Bool}
    (hanchor : word ∈ retainedCompletionWords C anchor)
    (hnotSingle :
      ¬ ∀ w : V,
        word ∈ retainedCompletionWords C w →
        w = anchor) :
    ∃ w : V,
      w ≠ anchor ∧
      word ∈ retainedCompletionWords C w ∧
      ∀ z : V,
        z ≠ anchor →
        word ∈ retainedCompletionWords C z →
        z = w := by
  push_neg at hnotSingle
  obtain ⟨w, hw, hwne⟩ := hnotSingle
  refine ⟨w, hwne, hw, ?_⟩
  intro z hz hzw
  exact additional_completion_blocker_unique
    C hanchor hzw hw hz hwne

theorem single_or_unique_additional_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {anchor : V}
    {word : Fin n → Bool}
    (hanchor : word ∈ retainedCompletionWords C anchor) :
    (∀ w : V,
      word ∈ retainedCompletionWords C w →
      w = anchor)
    ∨
    ∃ w : V,
      w ≠ anchor ∧
      word ∈ retainedCompletionWords C w ∧
      ∀ z : V,
        z ≠ anchor →
        word ∈ retainedCompletionWords C z →
        z = w := by
  by_cases hsingle :
      ∀ w : V,
        word ∈ retainedCompletionWords C w →
        w = anchor
  · exact Or.inl hsingle
  · exact Or.inr
      (exists_unique_additional_blocker_of_not_single
        C hanchor hsingle)

#print axioms additional_completion_blocker_unique
#print axioms exists_unique_additional_blocker_of_not_single
#print axioms single_or_unique_additional_blocker

end OrderedEdgeColoring
end JSP000404Research
