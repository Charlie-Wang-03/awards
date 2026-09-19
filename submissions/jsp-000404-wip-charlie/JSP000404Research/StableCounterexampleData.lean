import JSP000404Research.MergeZeroGain
import JSP000404Research.MergeCarry
import JSP000404Research.ZeroCarry
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Arithmetic certificate behind an exact-normalized stable interior example

This file records only the local quotient/remainder data of the explicit
six-ray example used to falsify the over-strong conjecture

  all incident deletions zero-gain + positive exponent -> hull vertex.

The geometric realization (six points on a circle around an interior centre)
is deliberately not claimed here.  What is formalized is the exact local data

  q = (2,0,1,0,1,0)
  r = (19/21, 1/15, 0, 1/15, 0, 2/35),

whose normalized gap lengths x=q+r sum to

  107/21 = 5 + 2/21.

Thus n=5 and delta=2/21<1/2.  Every adjacent remainder sum is below one, so
all binary carries vanish; every adjacent quotient pair contains a zero, so
every possible incident-ray merge has zero exponent gain.  Nevertheless the
positive support is three, marking the first regime not controlled by the
one-transition exposure argument.
-/

namespace JSP000404Research

open scoped BigOperators

def stableExampleQ : Fin 6 → ℕ :=
  ![2, 0, 1, 0, 1, 0]

noncomputable def stableExampleR : Fin 6 → ℝ :=
  ![(19 : ℝ) / 21, (1 : ℝ) / 15, 0, (1 : ℝ) / 15, 0, (2 : ℝ) / 35]

def succ6 (i : Fin 6) : Fin 6 :=
  ⟨(i.val + 1) % 6, Nat.mod_lt _ (by omega)⟩

theorem stableExample_positiveSupport :
    positiveSupport stableExampleQ = 3 := by
  native_decide

theorem stableExample_floorExcess :
    floorExcess stableExampleQ = 1 := by
  native_decide

theorem stableExample_quotient_sum :
    (∑ i, stableExampleQ i) = 4 := by
  native_decide

theorem stableExample_remainder_sum :
    (∑ i, stableExampleR i) = (23 : ℝ) / 21 := by
  norm_num [stableExampleR, Fin.sum_univ_succ]

theorem stableExample_total_gap :
    (∑ i, ((stableExampleQ i : ℕ) : ℝ) + stableExampleR i) =
      (107 : ℝ) / 21 := by
  norm_num [stableExampleQ, stableExampleR, Fin.sum_univ_succ]

theorem stableExample_delta_lower_branch :
    (0 : ℝ) ≤ (2 : ℝ) / 21 ∧ (2 : ℝ) / 21 < 1 / 2 := by
  norm_num

/-- Every adjacent quotient pair contains a zero. -/
theorem stableExample_adjacent_not_both_positive (i : Fin 6) :
    ¬ (1 ≤ stableExampleQ i ∧ 1 ≤ stableExampleQ (succ6 i)) := by
  fin_cases i <;>
    norm_num [stableExampleQ, succ6]

/-- Every adjacent fractional pair has zero carry. -/
theorem stableExample_adjacent_remainder_sum_lt_one (i : Fin 6) :
    stableExampleR i + stableExampleR (succ6 i) < 1 := by
  fin_cases i <;>
    norm_num [stableExampleR, succ6]

theorem stableExample_adjacent_carry_zero (i : Fin 6) :
    binaryCarry (stableExampleR i) (stableExampleR (succ6 i)) = 0 :=
  binaryCarry_eq_zero_of_lt
    (stableExample_adjacent_remainder_sum_lt_one i)

/-- Consequently every adjacent merge is zero-gain, independently of the
unchanged contribution from the other gaps. -/
theorem stableExample_every_merge_zero_gain
    (rest : ℕ) (i : Fin 6) :
    exponentAfterMerge
        rest
        (stableExampleQ i)
        (stableExampleQ (succ6 i))
        (binaryCarry (stableExampleR i) (stableExampleR (succ6 i)))
      =
    exponentBeforeMerge
        rest
        (stableExampleQ i)
        (stableExampleQ (succ6 i)) := by
  rw [stableExample_adjacent_carry_zero]
  apply (zero_gain_no_carry_iff).2
  fin_cases i <;>
    norm_num [stableExampleQ, succ6]

#print axioms stableExample_positiveSupport
#print axioms stableExample_floorExcess
#print axioms stableExample_total_gap
#print axioms stableExample_every_merge_zero_gain

end JSP000404Research
