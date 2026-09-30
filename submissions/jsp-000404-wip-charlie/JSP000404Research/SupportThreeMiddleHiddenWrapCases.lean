import JSP000404Research.SupportThreeMiddleHiddenCycleCertificate
import Mathlib.Tactic

/-!
# The five possible canonical-wrap positions in the middle-hidden cycle

For the explicit middle-hidden certificate,

  postTop ++ preTop = [r,b,c,d].

Thus the old canonical projective wrap can occur in exactly five positions
relative to the top-pinned cyclic order.  This file records that finite
classification without using any geometry or sign arguments.
-/

namespace JSP000404Research

theorem append_eq_four_cases
    {α : Type*}
    (post pre : List α)
    (r b c d : α)
    (h : post ++ pre = [r,b,c,d]) :
    (post = [] ∧ pre = [r,b,c,d]) ∨
    (post = [r] ∧ pre = [b,c,d]) ∨
    (post = [r,b] ∧ pre = [c,d]) ∨
    (post = [r,b,c] ∧ pre = [d]) ∨
    (post = [r,b,c,d] ∧ pre = []) := by
  cases post with
  | nil =>
      left
      exact ⟨rfl, by simpa using h⟩
  | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at h
      rcases h with ⟨hp, htail⟩
      subst p
      cases ps with
      | nil =>
          right; left
          exact ⟨rfl, by simpa using htail⟩
      | cons p₂ ps₂ =>
          simp only [List.cons_append, List.cons.injEq] at htail
          rcases htail with ⟨hp₂, htail⟩
          subst p₂
          cases ps₂ with
          | nil =>
              right; right; left
              exact ⟨rfl, by simpa using htail⟩
          | cons p₃ ps₃ =>
              simp only [List.cons_append, List.cons.injEq] at htail
              rcases htail with ⟨hp₃, htail⟩
              subst p₃
              cases ps₃ with
              | nil =>
                  right; right; right; left
                  exact ⟨rfl, by simpa using htail⟩
              | cons p₄ ps₄ =>
                  simp only [List.cons_append, List.cons.injEq] at htail
                  rcases htail with ⟨hp₄, htail⟩
                  subst p₄
                  have hnil : ps₄ = [] ∧ pre = [] := by
                    simpa using htail
                  rcases hnil with ⟨rfl, rfl⟩
                  right; right; right; right
                  exact ⟨rfl, rfl⟩

theorem eq_rotate_one_of_rotate_four_eq
    {α : Type*}
    (xs ys : List α)
    (hlen : xs.length = 5)
    (h : xs.rotate 4 = ys) :
    xs = ys.rotate 1 := by
  have hperiod : xs.rotate 5 = xs := by
    rw [List.rotate_eq_drop_append_take_mod]
    rw [hlen]
    norm_num
  have hback : (xs.rotate 4).rotate 1 = xs := by
    rw [List.rotate_rotate]
    exact hperiod
  calc
    xs = (xs.rotate 4).rotate 1 := hback.symm
    _ = ys.rotate 1 := by rw [h]

theorem eq_rotate_two_of_rotate_three_eq
    {α : Type*}
    (xs ys : List α)
    (hlen : xs.length = 5)
    (h : xs.rotate 3 = ys) :
    xs = ys.rotate 2 := by
  have hperiod : xs.rotate 5 = xs := by
    rw [List.rotate_eq_drop_append_take_mod]
    rw [hlen]
    norm_num
  have hback : (xs.rotate 3).rotate 2 = xs := by
    rw [List.rotate_rotate]
    exact hperiod
  calc
    xs = (xs.rotate 3).rotate 2 := hback.symm
    _ = ys.rotate 2 := by rw [h]

theorem eq_rotate_three_of_rotate_two_eq
    {α : Type*}
    (xs ys : List α)
    (hlen : xs.length = 5)
    (h : xs.rotate 2 = ys) :
    xs = ys.rotate 3 := by
  have hperiod : xs.rotate 5 = xs := by
    rw [List.rotate_eq_drop_append_take_mod]
    rw [hlen]
    norm_num
  have hback : (xs.rotate 2).rotate 3 = xs := by
    rw [List.rotate_rotate]
    exact hperiod
  calc
    xs = (xs.rotate 2).rotate 3 := hback.symm
    _ = ys.rotate 3 := by rw [h]

theorem eq_rotate_four_of_rotate_one_eq
    {α : Type*}
    (xs ys : List α)
    (hlen : xs.length = 5)
    (h : xs.rotate 1 = ys) :
    xs = ys.rotate 4 := by
  have hperiod : xs.rotate 5 = xs := by
    rw [List.rotate_eq_drop_append_take_mod]
    rw [hlen]
    norm_num
  have hback : (xs.rotate 1).rotate 4 = xs := by
    rw [List.rotate_rotate]
    exact hperiod
  calc
    xs = (xs.rotate 1).rotate 4 := hback.symm
    _ = ys.rotate 4 := by rw [h]

namespace MiddleHiddenPinnedCycleCertificate

theorem canonical_wrap_cases
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    {top i : V} {htopi : top ≠ i}
    {C : CentreProjectiveCycle hp i} {t : ℝ}
    (H : MiddleHiddenPinnedCycleCertificate hp top i htopi C t) :
    (H.postTop = [] ∧
      H.preTop = [H.r,H.b,H.c,H.d]) ∨
    (H.postTop = [H.r] ∧
      H.preTop = [H.b,H.c,H.d]) ∨
    (H.postTop = [H.r,H.b] ∧
      H.preTop = [H.c,H.d]) ∨
    (H.postTop = [H.r,H.b,H.c] ∧
      H.preTop = [H.d]) ∨
    (H.postTop = [H.r,H.b,H.c,H.d] ∧
      H.preTop = []) := by
  exact append_eq_four_cases
    H.postTop H.preTop H.r H.b H.c H.d H.tail_split

theorem canonical_wrap_index_cases
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    {top i : V} {htopi : top ≠ i}
    {C : CentreProjectiveCycle hp i} {t : ℝ}
    (H : MiddleHiddenPinnedCycleCertificate hp top i htopi C t) :
    H.postTop.length = 0 ∨
    H.postTop.length = 1 ∨
    H.postTop.length = 2 ∨
    H.postTop.length = 3 ∨
    H.postTop.length = 4 := by
  rcases H.canonical_wrap_cases with h0 | h1 | h2 | h3 | h4
  · left
    simp [h0.1]
  · right; left
    simp [h1.1]
  · right; right; left
    simp [h2.1]
  · right; right; right; left
    simp [h3.1]
  · right; right; right; right
    simp [h4.1]

#print axioms append_eq_four_cases
#print axioms eq_rotate_one_of_rotate_four_eq
#print axioms eq_rotate_two_of_rotate_three_eq
#print axioms eq_rotate_three_of_rotate_two_eq
#print axioms eq_rotate_four_of_rotate_one_eq
#print axioms MiddleHiddenPinnedCycleCertificate.canonical_wrap_cases
#print axioms MiddleHiddenPinnedCycleCertificate.canonical_wrap_index_cases

end MiddleHiddenPinnedCycleCertificate
end JSP000404Research
