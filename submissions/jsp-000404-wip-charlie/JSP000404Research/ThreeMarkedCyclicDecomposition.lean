import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Three marked elements in a cyclic list

Any three pairwise distinct marked elements of a finite list can be exposed in
cyclic order after rotating the first marked element to the head.
-/

namespace JSP000404Research

private theorem exists_append_cons_eq_of_mem
    {α : Type*} {a : α} {l : List α}
    (ha : a ∈ l) :
    ∃ pre post : List α, l = pre ++ a :: post := by
  induction l with
  | nil =>
      simp at ha
  | cons x xs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with hxa | ha
      · subst x
        exact ⟨[], xs, by simp⟩
      · obtain ⟨pre, post, hxs⟩ := ih ha
        exact ⟨x :: pre, post, by simp [hxs]⟩

theorem three_marked_cyclic_decomposition
    {α : Type*} [DecidableEq α]
    (l : List α)
    {a b c : α}
    (ha : a ∈ l)
    (hb : b ∈ l)
    (hc : c ∈ l)
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    ∃ k : ℕ,
      (
        ∃ X Y Z : List α,
          l.rotate k = a :: (X ++ b :: Y ++ c :: Z)
      )
      ∨
      (
        ∃ X Y Z : List α,
          l.rotate k = a :: (X ++ c :: Y ++ b :: Z)
      ) := by
  obtain ⟨pre,post,hl⟩ :=
    exists_append_cons_eq_of_mem ha
  let k := pre.length
  let tail := post ++ pre
  have hrot :
      l.rotate k = a :: tail := by
    dsimp [k,tail]
    rw [hl]
    simpa using
      (List.rotate_append_length_eq pre (a :: post))

  have hbTail : b ∈ tail := by
    have hb' : b ∈ pre ++ a :: post := by
      simpa [hl] using hb
    simp only [List.mem_append, List.mem_cons] at hb'
    rcases hb' with hbPre | hbA | hbPost
    · dsimp [tail]
      exact List.mem_append_right post hbPre
    · exact False.elim (hab hbA.symm)
    · dsimp [tail]
      exact List.mem_append_left pre hbPost
  have hcTail : c ∈ tail := by
    have hc' : c ∈ pre ++ a :: post := by
      simpa [hl] using hc
    simp only [List.mem_append, List.mem_cons] at hc'
    rcases hc' with hcPre | hcA | hcPost
    · dsimp [tail]
      exact List.mem_append_right post hcPre
    · exact False.elim (hac hcA.symm)
    · dsimp [tail]
      exact List.mem_append_left pre hcPost

  obtain ⟨U,V,hTailB⟩ :=
    exists_append_cons_eq_of_mem hbTail
  have hcSplit : c ∈ U ∨ c ∈ V := by
    rw [hTailB] at hcTail
    simp only [List.mem_append, List.mem_cons] at hcTail
    rcases hcTail with hcU | hcB | hcV
    · exact Or.inl hcU
    · exact False.elim (hbc hcB.symm)
    · exact Or.inr hcV
  refine ⟨k,?_⟩
  rcases hcSplit with hcU | hcV
  · right
    obtain ⟨X,Y,hU⟩ :=
      exists_append_cons_eq_of_mem hcU
    refine ⟨X,Y,V,?_⟩
    rw [hrot,hTailB,hU]
  · left
    obtain ⟨Y,Z,hV⟩ :=
      exists_append_cons_eq_of_mem hcV
    refine ⟨U,Y,Z,?_⟩
    rw [hrot,hTailB,hV]

#print axioms three_marked_cyclic_decomposition

end JSP000404Research
