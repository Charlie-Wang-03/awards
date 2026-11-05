import JSP000404Research.PlanarFirstThreshold
import JSP000404Research.OriginalProblemStatement

/-!
# The original lower bound on the first branch

The unconditional first-threshold theorem proves the three-point case and every N in the
first interval of the audited original formula. The second interval remains an independent
open obligation.
-/

namespace JSP000404Research

theorem first_threshold_formula (n : ℕ) :
    Real.pi - Real.pi / ((n : ℝ) + 1 / 2) =
      (1 - 2 / (2 * (n : ℝ) + 1)) * Real.pi := by
  have hfirst : (n : ℝ) + 1 / 2 ≠ 0 := by positivity
  have hsecond : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem original_lower_three : OriginalLowerBound 3 := by
  intro p hp
  obtain ⟨a, b, c, hab, hac, hbc, hangle⟩ :=
    planar_first_threshold_angle hp 1 (by decide) (by norm_num)
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  have hformula : Real.pi - Real.pi / ((1 : ℝ) + 1 / 2) = Real.pi / 3 := by ring
  simpa only [Nat.cast_one, hformula, Jsp404.alphaN] using hangle

/-- Every N in the first interval satisfies the exact original lower-bound statement. -/
theorem original_lower_first_branch {N n : ℕ} (hN : 4 ≤ N)
    (hindex : n = Nat.clog 2 N - 1)
    (hfirst : (N : ℝ) ≤ (2 : ℝ) ^ n + (2 : ℝ) ^ ((n : ℤ) - 2)) :
    OriginalLowerBound N := by
  have hlog : 1 < Nat.clog 2 N :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by norm_num; omega)
  have hn : 0 < n := by omega
  have hpower : 2 ^ n < N := by
    rw [hindex]
    exact Nat.pow_pred_clog_lt_self (by decide) (by omega)
  intro p hp
  obtain ⟨a, b, c, hab, hac, hbc, hangle⟩ :=
    planar_first_threshold_angle hp n hn (by simpa using hpower)
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  rw [Jsp404.alphaN_of_ge_four hN hindex, ite_eq_left hfirst]
  simpa only [first_threshold_formula] using hangle

#print axioms original_lower_three
#print axioms original_lower_first_branch

end JSP000404Research
