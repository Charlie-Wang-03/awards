import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Exact n=3 / five-centre no-top mass census

A bounded discrete profile on five actual centres, with no exponent-two
centre, has exponents in {0,1}. Its dyadic mass is exactly five plus
the number of exponent-one centres. Thus an overweight profile necessarily
has at least four exponent-one centres. This is a logical narrowing of
the unproved geometric residual, not a solution of the original problem.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Exact dyadic census of a finite 0/1 exponent profile. -/
theorem zero_one_dyadic_sum_eq_card_add_ones
    {V : Type*} [Fintype V]
    (k : V → ℕ)
    (hk : ∀ i : V, k i ≤ 1) :
    (∑ i : V, (2 : ℕ) ^ k i) =
      Fintype.card V +
      ((Finset.univ : Finset V).filter (fun i => k i = 1)).card := by
  classical
  have hpoint (i : V) :
      (2 : ℕ) ^ k i = 1 + (if k i = 1 then 1 else 0) := by
    have hcases : k i = 0 ∨ k i = 1 := by
      have := hk i
      omega
    rcases hcases with hzero | hone
    · simp [hzero]
    · simp [hone]
  calc
    (∑ i : V, (2 : ℕ) ^ k i) =
        ∑ i : V, (1 + (if k i = 1 then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpoint i
    _ = Fintype.card V +
        ((Finset.univ : Finset V).filter (fun i => k i = 1)).card := by
          simp [Finset.sum_add_distrib, Finset.sum_ite]

/-- An n=3 five-centre overweight profile with no top exponent has
at least four next-layer centres; this is a necessary, not sufficient,
geometric condition. -/
theorem five_centre_no_top_overweight_forces_four_next
    {V : Type*} [Fintype V]
    (k : V → ℕ)
    (hcard : Fintype.card V = 5)
    (hk : ∀ i : V, k i ≤ 1)
    (hover : 8 < (∑ i : V, (2 : ℕ) ^ k i)) :
    4 ≤ ((Finset.univ : Finset V).filter (fun i => k i = 1)).card := by
  rw [zero_one_dyadic_sum_eq_card_add_ones k hk, hcard] at hover
  omega

/-- Conversely, at most three next-layer centres make an n=3
no-top five-centre profile dyadically admissible. -/
theorem five_centre_no_top_at_most_three_next_capacity
    {V : Type*} [Fintype V]
    (k : V → ℕ)
    (hcard : Fintype.card V = 5)
    (hk : ∀ i : V, k i ≤ 1)
    (hnext : ((Finset.univ : Finset V).filter (fun i => k i = 1)).card ≤ 3) :
    (∑ i : V, (2 : ℕ) ^ k i) ≤ 8 := by
  rw [zero_one_dyadic_sum_eq_card_add_ones k hk, hcard]
  omega

#print axioms zero_one_dyadic_sum_eq_card_add_ones
#print axioms five_centre_no_top_overweight_forces_four_next
#print axioms five_centre_no_top_at_most_three_next_capacity

end JSP000404Research
