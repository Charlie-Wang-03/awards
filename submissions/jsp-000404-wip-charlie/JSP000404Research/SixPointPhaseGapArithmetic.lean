import JSP000404Research.CyclicProjectiveGaps
import Mathlib.Tactic

/-!
# Fifteen-direction gap arithmetic for the six-point terminal

A six-point configuration has at most C(6,2)=15 unoriented edge directions.
The global projective direction circle has circumference pi.

This file isolates the numerical part of the large-n phase-gap argument.

* A nonempty cyclic direction list with at most 15 entries has a cyclic gap
  of length at least pi/15.
* If n>=7 and 0<=delta<1/2, then

      15*delta < n+delta.

  Hence for t=n+delta and lambda=pi/t,

      delta*lambda < pi/15.

So a fifteen-direction cycle has enough empty projective room to place the
extra delta part of one long (1+delta)-cell.
-/

namespace JSP000404Research

open Real

/-- Strict sum bound for a nonempty finite real list whose entries are all
strictly below one common threshold. -/
theorem list_sum_lt_length_mul_of_forall_lt
    (xs : List ℝ) (c : ℝ)
    (hne : xs ≠ [])
    (hall : ∀ x ∈ xs, x < c) :
    xs.sum < (xs.length : ℝ) * c := by
  induction xs with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs ih =>
      have hx : x < c := hall x (by simp)
      by_cases htail : xs = []
      · subst xs
        simpa using hx
      · have htailAll : ∀ y ∈ xs, y < c := by
          intro y hy
          exact hall y (by simp [hy])
        have hih := ih htail htailAll
        simp only [List.sum_cons, List.length_cons, Nat.cast_add,
          Nat.cast_one]
        nlinarith

/-- Any nonempty nonnegative cyclic gap list of total mass pi with at most
15 gaps has one gap of size at least pi/15. -/
theorem exists_gap_ge_pi_div_fifteen_of_sum_pi
    (gaps : List ℝ)
    (hne : gaps ≠ [])
    (hcard : gaps.length ≤ 15)
    (hsum : gaps.sum = Real.pi) :
    ∃ g ∈ gaps, Real.pi / 15 ≤ g := by
  by_contra hnone
  push_neg at hnone
  have hall : ∀ g ∈ gaps, g < Real.pi / 15 := by
    intro g hg
    exact lt_of_not_ge (hnone g hg)
  have hlt :=
    list_sum_lt_length_mul_of_forall_lt
      gaps (Real.pi / 15) hne hall
  have hlenR : (gaps.length : ℝ) ≤ 15 := by
    exact_mod_cast hcard
  have hpi15 : 0 < Real.pi / 15 := by positivity
  have hmul :
      (gaps.length : ℝ) * (Real.pi / 15)
        ≤ 15 * (Real.pi / 15) :=
    mul_le_mul_of_nonneg_right hlenR hpi15.le
  have hright : 15 * (Real.pi / 15) = Real.pi := by
    field_simp
  rw [hsum, hright] at hlt hmul
  linarith

/-- Projective-cycle specialization. -/
theorem exists_projectiveGap_ge_pi_div_fifteen
    (angles : List ℝ)
    (hne : angles ≠ [])
    (hcard : angles.length ≤ 15) :
    ∃ g ∈ projectiveGaps angles,
      Real.pi / 15 ≤ g := by
  have hgapsNe : projectiveGaps angles ≠ [] := by
    intro h
    have hlen := projectiveGaps_length angles
    rw [h] at hlen
    simp at hlen
    exact hne (List.length_eq_zero.mp hlen)
  have hgapsCard :
      (projectiveGaps angles).length ≤ 15 := by
    rw [projectiveGaps_length]
    exact hcard
  cases angles with
  | nil =>
      exact False.elim (hne rfl)
  | cons a xs =>
      exact exists_gap_ge_pi_div_fifteen_of_sum_pi
        (projectiveGaps (a :: xs))
        hgapsNe hgapsCard projectiveGaps_sum

/-- Lower-branch arithmetic behind the six-point large-n threshold. -/
theorem fifteen_mul_delta_lt_n_add_delta
    {n : ℕ} {delta : ℝ}
    (hn : 7 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2) :
    15 * delta < (n : ℝ) + delta := by
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- In physical projective angle units, the extra delta-part of the long cell
is shorter than pi/15. -/
theorem delta_mul_lambda_lt_pi_div_fifteen
    {n : ℕ} {delta t lam : ℝ}
    (hn : 7 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t) :
    delta * lam < Real.pi / 15 := by
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by omega)
    linarith
  have hnum :=
    fifteen_mul_delta_lt_n_add_delta
      hn hdelta0 hdeltaHalf
  rw [← ht] at hnum
  rw [hlam]
  have hpi : 0 < Real.pi := Real.pi_pos
  field_simp [ne_of_gt htpos]
  nlinarith

#print axioms exists_projectiveGap_ge_pi_div_fifteen
#print axioms fifteen_mul_delta_lt_n_add_delta
#print axioms delta_mul_lambda_lt_pi_div_fifteen

end JSP000404Research
