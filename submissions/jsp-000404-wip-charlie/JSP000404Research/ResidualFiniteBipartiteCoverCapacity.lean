import Mathlib.Tactic

/-!
# Non-reused finite bipartite vertex-cover payment certificate

For a finite collection of sources s with LEFT and RIGHT labels
which are individually injective, any pair of labelled vertex sets
(A,B) covering EVERY actual source edge satisfies |sources|<=|A|+|B|.

The proof actually INJECTS each source into ONE of the two disjoint
tagged cover pools, never taking credit from both sides for one
source. This is the elementary matching/vertex-cover inequality,
with no unproved appeal to König's theorem.

A later geometric specialization will use lower bridge/reverse-flip
slots as left labels and upper bridge/forward-flip slots as right labels.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A certified finite bipartite matching cannot exceed any
explicit vertex cover. The two label maps are injective on the
actual source collection; credit for each source is charged to
exactly one tagged endpoint of the cover. -/
theorem finset_two_injective_labels_card_le_cover
    {S L R : Type*} [DecidableEq S] [DecidableEq L] [DecidableEq R]
    (sources : Finset S)
    (left : S → L) (right : S → R)
    (hleft : ∀ s ∈ sources, ∀ t ∈ sources,
      left s = left t → s = t)
    (hright : ∀ s ∈ sources, ∀ t ∈ sources,
      right s = right t → s = t)
    (A : Finset L) (B : Finset R)
    (hcover : ∀ s ∈ sources, left s ∈ A ∨ right s ∈ B) :
    sources.card ≤ A.card + B.card := by
  classical
  let f : {s : S // s ∈ sources} → Sum L R :=
    fun s => if left s.1 ∈ A
      then Sum.inl (left s.1) else Sum.inr (right s.1)
  have hinj : Function.Injective f := by
    intro s t heq
    apply Subtype.ext
    have hval : (if left s.1 ∈ A
        then Sum.inl (left s.1) else Sum.inr (right s.1)) =
      (if left t.1 ∈ A
        then Sum.inl (left t.1) else Sum.inr (right t.1)) := heq
    by_cases hs : left s.1 ∈ A
    · by_cases ht : left t.1 ∈ A
      · simp only [if_pos hs, if_pos ht] at hval
        exact hleft s.1 s.2 t.1 t.2 (Sum.inl.inj hval)
      · simp only [if_pos hs, if_neg ht] at hval
        cases hval
    · by_cases ht : left t.1 ∈ A
      · simp only [if_neg hs, if_pos ht] at hval
        cases hval
      · simp only [if_neg hs, if_neg ht] at hval
        exact hright s.1 s.2 t.1 t.2 (Sum.inr.inj hval)
  have hsub :
      (Finset.univ : Finset {s : S // s ∈ sources}).image f ⊆
        (A.image Sum.inl) ∪ (B.image Sum.inr) := by
    intro x hx
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hx
    by_cases ha : left s.1 ∈ A
    · have hf : f s = Sum.inl (left s.1) := by simp [f, ha]
      rw [hf]
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨left s.1, ha, rfl⟩))
    · have hb : right s.1 ∈ B := (hcover s.1 s.2).resolve_left ha
      have hf : f s = Sum.inr (right s.1) := by simp [f, ha]
      rw [hf]
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨right s.1, hb, rfl⟩))
  calc
    sources.card =
        (Finset.univ : Finset {s : S // s ∈ sources}).card := by simp
    _ = ((Finset.univ : Finset {s : S // s ∈ sources}).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((A.image Sum.inl) ∪ (B.image Sum.inr)).card :=
      Finset.card_le_card hsub
    _ ≤ (A.image Sum.inl).card + (B.image Sum.inr).card :=
      Finset.card_union_le _ _
    _ = A.card + B.card := by
      have hL : (A.image (Sum.inl : L → Sum L R)).card = A.card :=
        Finset.card_image_of_injective _
          (fun _ _ h => Sum.inl.inj h)
      have hR : (B.image (Sum.inr : R → Sum L R)).card = B.card :=
        Finset.card_image_of_injective _
          (fun _ _ h => Sum.inr.inj h)
      rw [hL, hR]

#print axioms finset_two_injective_labels_card_le_cover

end OrderedEdgeColoring
end JSP000404Research
