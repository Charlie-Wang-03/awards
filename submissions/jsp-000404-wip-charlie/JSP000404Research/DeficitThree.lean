import JSP000404Research.GapRemainder
import JSP000404Research.SharpDeficit
import Mathlib.Tactic

/-!
# Structure of Sendov deficit three

For n >= 4, the exact zero-carry identity

  ell = (n - sum q) + positiveSupport q

makes ell = 3 completely rigid.  The zero-support case would force ell=n and
is excluded by n>=4.  Hence exactly one of the following holds:

* support = 1 and sum q = n-2;
* support = 2 and sum q = n-1;
* support = 3 and sum q = n.

The corresponding total scaled zero-gap budgets are

  delta+2, delta+1, delta.

The support-three branch is therefore again a full-quotient-mass branch: all
zero quotient gaps together consume only the fractional remainder delta.
-/

namespace JSP000404Research

open scoped BigOperators

theorem positiveSupport_pos_of_deficit_three
    {I : Type*} [Fintype I]
    (q : I → ℕ) (n : ℕ)
    (hn : 4 ≤ n)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 3) :
    0 < positiveSupport q := by
  by_contra hnot
  have hp0 : positiveSupport q = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hq0 := positiveSupport_eq_zero_imp q hp0
  have hE0 : floorExcess q = 0 := by
    simp [floorExcess, hq0]
  rw [hE0] at hell
  omega

theorem deficit_three_structure
    {I : Type*} [Fintype I]
    (q : I → ℕ) (n : ℕ)
    (hn : 4 ≤ n)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 3) :
    (positiveSupport q = 1 ∧ (∑ i, q i) = n - 2) ∨
    (positiveSupport q = 2 ∧ (∑ i, q i) = n - 1) ∨
    (positiveSupport q = 3 ∧ (∑ i, q i) = n) := by
  have hdec := deficit_eq_floorDefect_add_support q n hQ
  have hp_le : positiveSupport q ≤ 3 := by
    rw [← hell, hdec]
    omega
  have hp_pos :=
    positiveSupport_pos_of_deficit_three q n hn hQ hell
  have hcases :
      positiveSupport q = 1 ∨
      positiveSupport q = 2 ∨
      positiveSupport q = 3 := by
    omega
  rcases hcases with hp1 | hp2 | hp3
  · left
    constructor
    · exact hp1
    · rw [hell, hdec, hp1] at *
      omega
  · right
    left
    constructor
    · exact hp2
    · rw [hell, hdec, hp2] at *
      omega
  · right
    right
    constructor
    · exact hp3
    · rw [hell, hdec, hp3] at *
      omega

theorem deficit_three_zero_gap_budget
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 4 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hgap : (∑ i, gap i) = 1)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 3)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i) :
    (positiveSupport q = 1 ∧
      (∑ i, q i) = n - 2 ∧
      t * zeroGapMass gap q ≤ delta + 2) ∨
    (positiveSupport q = 2 ∧
      (∑ i, q i) = n - 1 ∧
      t * zeroGapMass gap q ≤ delta + 1) ∨
    (positiveSupport q = 3 ∧
      (∑ i, q i) = n ∧
      t * zeroGapMass gap q ≤ delta) := by
  rcases deficit_three_structure q n hn hQ hell with h1 | h2 | h3
  · left
    refine ⟨h1.1, h1.2, ?_⟩
    have hb :=
      zeroGapMass_scaled_le_delta_add_deficit_sub_support
        gap q n 3 delta t ht hgap hQ rfl hfloor
    rw [h1.1] at hb
    norm_num at hb ⊢
    exact hb
  · right
    left
    refine ⟨h2.1, h2.2, ?_⟩
    have hb :=
      zeroGapMass_scaled_le_delta_add_deficit_sub_support
        gap q n 3 delta t ht hgap hQ rfl hfloor
    rw [h2.1] at hb
    norm_num at hb ⊢
    exact hb
  · right
    right
    refine ⟨h3.1, h3.2, ?_⟩
    exact zeroGapMass_scaled_le_delta
      gap q n delta t ht hgap h3.2 hfloor

theorem deficit_three_support_three_width_lt_half
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 4 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hgap : (∑ i, gap i) = 1)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 3)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    (hsupport : positiveSupport q = 3) :
    t * zeroGapMass gap q < (1 : ℝ) / 2 := by
  rcases deficit_three_zero_gap_budget
      gap q n delta t hn ht hgap hQ hell hfloor with
    h1 | h2 | h3
  · omega
  · omega
  · have hb := h3.2.2
    linarith

#print axioms positiveSupport_pos_of_deficit_three
#print axioms deficit_three_structure
#print axioms deficit_three_zero_gap_budget
#print axioms deficit_three_support_three_width_lt_half

end JSP000404Research
