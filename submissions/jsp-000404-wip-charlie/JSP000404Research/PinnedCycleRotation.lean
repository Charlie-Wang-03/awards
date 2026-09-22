import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Canonical list decomposition at a specified index

Cyclic ray arguments repeatedly need to decompose several aligned lists at the
same position.  This file packages the canonical take/get/drop decomposition

  l = l.take k ++ l[k] :: l.drop (k+1)

together with exact prefix length.

It also records the corresponding rotation identity: cutting a list at the
displayed element moves that element to the front.
-/

namespace JSP000404Research

theorem exists_take_cons_drop_decomposition
    {α : Type*}
    (l : List α) (k : ℕ)
    (hk : k < l.length) :
    ∃ pre x post,
      l = pre ++ x :: post ∧
      pre.length = k := by
  let pre := l.take k
  let x := l[k]
  let post := l.drop (k + 1)
  refine ⟨pre, x, post, ?_, ?_⟩
  · dsimp [pre, x, post]
    have htake :
        l.take k ++ [l[k]] = l.take (k + 1) :=
      List.take_concat_get' l k hk
    have hfull :
        l.take (k + 1) ++ l.drop (k + 1) = l :=
      List.take_append_drop (k + 1) l
    rw [← hfull, ← htake]
    simp [List.append_assoc]
  · dsimp [pre]
    simp [List.length_take, Nat.min_eq_left hk.le]

theorem rotate_displayed_element_to_front
    {α : Type*}
    (pre post : List α) (x : α) :
    (pre ++ x :: post).rotate pre.length =
      x :: (post ++ pre) := by
  rw [List.rotate_append_length_eq]
  simp [List.append_assoc]

/-- Same-index decompositions for two equal-length lists. -/
theorem simultaneous_decomposition_at_index
    {α β : Type*}
    (l₁ : List α) (l₂ : List β)
    (hlen : l₁.length = l₂.length)
    (k : ℕ) (hk : k < l₁.length) :
    ∃ pre₁ x₁ post₁ pre₂ x₂ post₂,
      l₁ = pre₁ ++ x₁ :: post₁ ∧
      l₂ = pre₂ ++ x₂ :: post₂ ∧
      pre₁.length = k ∧
      pre₂.length = k := by
  obtain ⟨pre₁, x₁, post₁, h₁, hp₁⟩ :=
    exists_take_cons_drop_decomposition l₁ k hk
  have hk₂ : k < l₂.length := by
    rwa [← hlen]
  obtain ⟨pre₂, x₂, post₂, h₂, hp₂⟩ :=
    exists_take_cons_drop_decomposition l₂ k hk₂
  exact ⟨pre₁, x₁, post₁, pre₂, x₂, post₂,
    h₁, h₂, hp₁, hp₂⟩


theorem exists_append_cons_of_mem
    {α : Type*} {x : α} {l : List α}
    (hx : x ∈ l) :
    ∃ pre post, l = pre ++ x :: post := by
  induction l with
  | nil =>
      simp at hx
  | cons a l ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨[], l, rfl⟩
      · obtain ⟨pre, post, h⟩ := ih hx
        refine ⟨a :: pre, post, ?_⟩
        simp [h]

/-- Once one list has been split at an element, any equal-length companion
list admits a distinguished entry at the same prefix length. -/
theorem companion_decomposition_at_prefix
    {α β : Type*}
    (pre : List α) (x : α) (post : List α)
    (l₂ : List β)
    (hlen : (pre ++ x :: post).length = l₂.length) :
    ∃ pre₂ y post₂,
      l₂ = pre₂ ++ y :: post₂ ∧
      pre₂.length = pre.length := by
  have hk :
      pre.length < l₂.length := by
    rw [← hlen]
    simp
  obtain ⟨pre₂, y, post₂, h₂, hp₂⟩ :=
    exists_take_cons_drop_decomposition l₂ pre.length hk
  exact ⟨pre₂, y, post₂, h₂, hp₂⟩

#print axioms exists_take_cons_drop_decomposition
#print axioms exists_append_cons_of_mem
#print axioms companion_decomposition_at_prefix
#print axioms rotate_displayed_element_to_front
#print axioms simultaneous_decomposition_at_index

end JSP000404Research
