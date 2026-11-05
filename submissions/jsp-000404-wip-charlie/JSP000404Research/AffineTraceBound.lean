import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# The two-dimensional affine certificate inequality

For a positive definite certificate C=[[a,b],[b,c]] and positive definite
metric Q=[[x,y],[y,z]] of determinant one, write det C=s^2. A sum-of-squares
identity proves tr(QC)>=2s. Its equality conditions also isolate the minimizing
metric when s is positive. These scalar statements use explicit determinant
and positivity hypotheses.
-/

namespace JSP000404Research

theorem affine_trace_sum_of_squares {a b c x y z s : ℝ}
    (hQ : x * z - y ^ 2 = 1) (hC : a * c - b ^ 2 = s ^ 2) :
    a * z * (a * x + 2 * b * y + c * z - 2 * s) =
      (a - s * z) ^ 2 + (a * y + b * z) ^ 2 := by
  linear_combination a ^ 2 * hQ + z ^ 2 * hC

theorem affine_trace_lower_bound {a b c x y z s : ℝ}
    (ha : 0 < a) (hz : 0 < z)
    (hQ : x * z - y ^ 2 = 1) (hC : a * c - b ^ 2 = s ^ 2) :
    2 * s ≤ a * x + 2 * b * y + c * z := by
  have hidentity := affine_trace_sum_of_squares hQ hC
  have hnonneg : 0 ≤ a * z * (a * x + 2 * b * y + c * z - 2 * s) := by
    rw [hidentity]
    positivity
  have h := nonneg_of_mul_nonneg_right hnonneg (mul_pos ha hz)
  linarith

theorem affine_trace_equality_iff {a b c x y z s : ℝ}
    (ha : 0 < a) (hz : 0 < z)
    (hQ : x * z - y ^ 2 = 1) (hC : a * c - b ^ 2 = s ^ 2) :
    a * x + 2 * b * y + c * z = 2 * s ↔ a = s * z ∧ a * y + b * z = 0 := by
  have hidentity := affine_trace_sum_of_squares hQ hC
  constructor
  · intro heq
    rw [heq, sub_self, mul_zero] at hidentity
    have hfirst := sq_nonneg (a - s * z)
    have hsecond := sq_nonneg (a * y + b * z)
    have hf : (a - s * z) ^ 2 = 0 := by linarith
    have hs : (a * y + b * z) ^ 2 = 0 := by linarith
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hf), sq_eq_zero_iff.mp hs⟩
  · rintro ⟨hfirst, hsecond⟩
    rw [show a - s * z = 0 by linarith, hsecond,
      zero_pow (by decide : 2 ≠ 0), add_zero] at hidentity
    have haz : a * z ≠ 0 := ne_of_gt (mul_pos ha hz)
    have hzero : a * x + 2 * b * y + c * z - 2 * s = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left haz
      exact hidentity
    linarith

#print axioms affine_trace_sum_of_squares
#print axioms affine_trace_lower_bound
#print axioms affine_trace_equality_iff

end JSP000404Research
