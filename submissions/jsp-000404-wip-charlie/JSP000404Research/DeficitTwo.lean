import JSP000404Research.GapRemainder
import JSP000404Research.SharpDeficit
import Mathlib.Tactic

/-!
# Structure of Sendov deficit two

For n >= 3, the exact decomposition

  ell = (n - sum q) + positiveSupport q

makes ell = 2 completely rigid.  There are only two cases:

* one positive quotient gap and quotient sum n-1;
* two positive quotient gaps and quotient sum n.

The degenerate zero-support possibility would force ell=n, hence only occurs
when n=2 and is excluded here.

The corresponding zero-gap width budgets are delta+1 and delta respectively.
-/

namespace JSP000404Research

open scoped BigOperators

theorem positiveSupport_pos_of_deficit_two
    {I : Type*} [Fintype I]
    (q : I → ℕ) (n : ℕ)
    (hn : 3 ≤ n)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 2) :
    0 < positiveSupport q := by
  by_contra hnot
  have hp0 : positiveSupport q = 0 := Nat.eq_zero_of_not_pos hnot
  have hq0 := positiveSupport_eq_zero_imp q hp0
  have hE0 : floorExcess q = 0 := by
    simp [floorExcess, hq0]
  rw [hE0] at hell
  omega

/-- Complete arithmetic classification of an ell=2 centre for n>=3. -/
theorem deficit_two_structure
    {I : Type*} [Fintype I]
    (q : I → ℕ) (n : ℕ)
    (hn : 3 ≤ n)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 2) :
    (positiveSupport q = 1 ∧ (∑ i, q i) = n - 1) ∨
    (positiveSupport q = 2 ∧ (∑ i, q i) = n) := by
  have hdec := deficit_eq_floorDefect_add_support q n hQ
  have hp_le : positiveSupport q ≤ 2 := by
    rw [← hell, hdec]
    omega
  have hp_pos := positiveSupport_pos_of_deficit_two q n hn hQ hell
  rcases Nat.eq_one_or_two_of_pos_of_le_two hp_pos hp_le with hp1 | hp2
  · left
    constructor
    · exact hp1
    · rw [hell, hdec, hp1] at *
      omega
  · right
    constructor
    · exact hp2
    · rw [hell, hdec, hp2] at *
      omega

/-- Width-budget form of the two ell=2 cases. -/
theorem deficit_two_zero_gap_budget
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 3 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hgap : (∑ i, gap i) = 1)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 2)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i) :
    (positiveSupport q = 1 ∧
      (∑ i, q i) = n - 1 ∧
      t * zeroGapMass gap q ≤ delta + 1) ∨
    (positiveSupport q = 2 ∧
      (∑ i, q i) = n ∧
      t * zeroGapMass gap q ≤ delta) := by
  rcases deficit_two_structure q n hn hQ hell with h1 | h2
  · left
    refine ⟨h1.1, h1.2, ?_⟩
    have hb :=
      zeroGapMass_scaled_le_delta_add_deficit_sub_support
        gap q n 2 delta t ht hgap hQ rfl hfloor
    rw [h1.1] at hb
    norm_num at hb ⊢
    exact hb
  · right
    refine ⟨h2.1, h2.2, ?_⟩
    exact zeroGapMass_scaled_le_delta
      gap q n delta t ht hgap h2.2 hfloor

/-- In the lower branch delta<1/2, the one-positive case has total zero-gap
scaled width strictly below 3/2. -/
theorem deficit_two_one_support_width_lt_three_halves
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 3 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hgap : (∑ i, gap i) = 1)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 2)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    (hp : positiveSupport q = 1) :
    t * zeroGapMass gap q < (3 : ℝ) / 2 := by
  have hb :=
    zeroGapMass_scaled_le_delta_add_deficit_sub_support
      gap q n 2 delta t ht hgap hQ rfl hfloor
  rw [hp] at hb
  norm_num at hb
  linarith

/-- In the two-positive case, the total internal cluster width is below 1/2. -/
theorem deficit_two_two_support_width_lt_half
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 3 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hgap : (∑ i, gap i) = 1)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 2)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    (hp : positiveSupport q = 2) :
    t * zeroGapMass gap q < (1 : ℝ) / 2 := by
  rcases deficit_two_zero_gap_budget
      gap q n delta t hn ht hgap hQ hell hfloor with h1 | h2
  · omega
  · have hb := h2.2.2
    linarith

#print axioms positiveSupport_pos_of_deficit_two
#print axioms deficit_two_structure
#print axioms deficit_two_zero_gap_budget
#print axioms deficit_two_one_support_width_lt_three_halves
#print axioms deficit_two_two_support_width_lt_half

end JSP000404Research
