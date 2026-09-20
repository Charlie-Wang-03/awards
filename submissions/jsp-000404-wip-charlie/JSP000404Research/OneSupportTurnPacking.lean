import JSP000404Research.DyadicTurnCost
import Mathlib.Tactic

/-!
# Packing one-support transition gaps pays their full dyadic mass

Suppose a finite family of centres has:

* exponent k_i < n,
* positive transition quotient q_i = k_i+1,
* normalized transition gap g_i,
* q_i <= t*g_i,
* t = n+delta with 0 <= delta < 1/2,
* total normalized transition-gap length at most 2.

Then

  sum q_i <= 2*n

by a real-length estimate followed by integer rounding.  The dyadic turn-cost
theorem therefore yields

  sum 2^(k_i) <= 2^n.

Thus the entire one-support regime reduces geometrically to one statement:
its transition / exterior-turn gaps pack into normalized total length at most
two (the full 2*pi turning budget divided by pi).
-/

namespace JSP000404Research

open scoped BigOperators

/-- Integer turn-cost budget from normalized gap packing. -/
theorem sum_quotient_le_two_n_of_transition_gap_packing
    {I : Type*} [Fintype I]
    (quotient : I → ℕ)
    (gap : I → ℝ)
    (n : ℕ) (delta t : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (halign : ∀ i, (quotient i : ℝ) ≤ t * gap i)
    (hgapSum : (∑ i, gap i) ≤ 2) :
    (∑ i, quotient i) ≤ 2 * n := by
  have ht0 : 0 ≤ t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hsumReal :
      (∑ i, (quotient i : ℝ)) ≤
        ∑ i, t * gap i :=
    Finset.sum_le_sum fun i _ => halign i
  have hfactor :
      (∑ i, t * gap i) = t * ∑ i, gap i := by
    rw [Finset.mul_sum]
  rw [hfactor] at hsumReal
  have hpack :
      t * (∑ i, gap i) ≤ t * 2 :=
    mul_le_mul_of_nonneg_left hgapSum ht0
  have hupper :
      t * 2 < (2 * n : ℕ) + 1 := by
    rw [ht]
    push_cast
    linarith
  have hcast :
      (((∑ i, quotient i) : ℕ) : ℝ) =
        ∑ i, (quotient i : ℝ) := by
    norm_num
  have hlt :
      (((∑ i, quotient i) : ℕ) : ℝ) <
        (((2 * n + 1 : ℕ) : ℕ) : ℝ) := by
    rw [hcast]
    exact hsumReal.trans_le hpack |>.trans_lt (by
      simpa using hupper)
  have hnat :
      (∑ i, quotient i) < 2 * n + 1 := by
    exact_mod_cast hlt
  omega

/-- Full dyadic conclusion from packed transition gaps. -/
theorem dyadic_sum_le_two_pow_of_transition_gap_packing
    {I : Type*} [Fintype I]
    (exponent quotient : I → ℕ)
    (gap : I → ℝ)
    (n : ℕ) (delta t : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hexp : ∀ i, exponent i < n)
    (hq : ∀ i, quotient i = exponent i + 1)
    (halign : ∀ i, (quotient i : ℝ) ≤ t * gap i)
    (hgapSum : (∑ i, gap i) ≤ 2) :
    (∑ i, 2 ^ exponent i) ≤ 2 ^ n := by
  have hqsum :
      (∑ i, quotient i) ≤ 2 * n :=
    sum_quotient_le_two_n_of_transition_gap_packing
      quotient gap n delta t
      hn hdelta0 hdeltaHalf ht halign hgapSum
  apply dyadic_sum_le_two_pow_of_turn_cost
    exponent n hn hexp
  have heq :
      (∑ i, (exponent i + 1)) =
        ∑ i, quotient i := by
    apply Finset.sum_congr rfl
    intro i _
    exact (hq i).symm
  rw [heq]
  exact hqsum

#print axioms sum_quotient_le_two_n_of_transition_gap_packing
#print axioms dyadic_sum_le_two_pow_of_transition_gap_packing

end JSP000404Research
