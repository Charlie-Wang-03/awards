import JSP000404Research.BooleanFlipCore
import Mathlib.Tactic

/-!
# Lightweight translated retained completion cubes

Translate one retained completion cube by flipping a fixed retained coordinate.
This is the only block-level Boolean operation required by WholeCubeQTPair.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def translatedCompletionWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n) :
    Finset (Fin n → Bool) :=
  (retainedCompletionWords C v).image
    (fun word => flipBoolWordAt word c)

theorem mem_translatedCompletionWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n)
    (word : Fin n → Bool) :
    word ∈ translatedCompletionWords C v c ↔
      flipBoolWordAt word c ∈ retainedCompletionWords C v := by
  classical
  unfold translatedCompletionWords
  constructor
  · intro h
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
    simpa [flipBoolWordAt_involutive] using hx
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨flipBoolWordAt word c, h, ?_⟩
    exact flipBoolWordAt_involutive c word

theorem translatedCompletionWords_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n) :
    (translatedCompletionWords C v c).card =
      (retainedCompletionWords C v).card := by
  classical
  unfold translatedCompletionWords
  rw [Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  exact flipBoolWordAt_injective c hxy

theorem translatedCompletionWords_disjoint_original_of_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {c : Fin n}
    (hc : c ∈ retainedActive C v) :
    Disjoint
      (translatedCompletionWords C v c)
      (retainedCompletionWords C v) := by
  classical
  rw [Finset.disjoint_left]
  intro word htrans horig
  rw [mem_translatedCompletionWords C v c word] at htrans
  exact flip_active_not_mem_completion C horig hc htrans

#print axioms mem_translatedCompletionWords
#print axioms translatedCompletionWords_card
#print axioms translatedCompletionWords_disjoint_original_of_active

end OrderedEdgeColoring
end JSP000404Research
