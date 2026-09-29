import Mathlib.Tactic

/-!
# Transition quotient arithmetic

This module isolates the real/natural arithmetic behind the current
support-three terminal without importing the older projective-ray stack.

If
  q = floor(t * g / pi) <= n-2
with t = n+delta and lambda = pi/t, then
  g < (n-1)*lambda.

No geometric statement is made here; the later ray-angle bridge may consume
this lemma once the corresponding geometry module is on a clean Lean-4.34
dependency path.
-/

namespace JSP000404Research

open Real

theorem normalized_gap_lt_n_sub_one_mul_lam_of_floor_le
    {n : ℕ} {t lam g : ℝ}
    (hn2 : 2 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (hg0 : 0 ≤ g)
    (hq :
      Nat.floor (t * (g / Real.pi)) ≤ n - 2) :
    g < ((n - 1 : ℕ) : ℝ) * lam := by
  let x : ℝ := t * (g / Real.pi)
  have hxlt :
      x < (Nat.floor x : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hqR :
      (Nat.floor x : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by
    exact_mod_cast hq
  have hn2cast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn2]
    norm_num
  have hn1cast :
      ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hxbound :
      x < ((n - 1 : ℕ) : ℝ) := by
    calc
      x < (Nat.floor x : ℝ) + 1 := hxlt
      _ ≤ ((n - 2 : ℕ) : ℝ) + 1 := by linarith
      _ = ((n - 1 : ℕ) : ℝ) := by
        rw [hn2cast, hn1cast]
        ring
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcoef : 0 < t / Real.pi := div_pos htpos hpi
  have hxrewrite :
      x = (t / Real.pi) * g := by
    dsimp [x]
    ring
  have hscaled :
      (t / Real.pi) * g < ((n - 1 : ℕ) : ℝ) := by
    simpa [hxrewrite] using hxbound
  have hdiv :
      g < ((n - 1 : ℕ) : ℝ) / (t / Real.pi) := by
    exact (lt_div_iff₀ hcoef).2 (by
      simpa [mul_comm] using hscaled)
  rw [hlam]
  have htne : t ≠ 0 := ne_of_gt htpos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  calc
    g < ((n - 1 : ℕ) : ℝ) / (t / Real.pi) := hdiv
    _ = ((n - 1 : ℕ) : ℝ) * (Real.pi / t) := by
      field_simp [htne, hpine]

/-- Version specialized to t=n+delta.  The equality is retained because later
geometric code uses that normalization explicitly. -/
theorem normalized_gap_lt_n_sub_one_mul_lam_of_floor_le_sendov
    {n : ℕ} {delta t lam g : ℝ}
    (hn2 : 2 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hg0 : 0 ≤ g)
    (hq :
      Nat.floor (t * (g / Real.pi)) ≤ n - 2) :
    g < ((n - 1 : ℕ) : ℝ) * lam := by
  exact normalized_gap_lt_n_sub_one_mul_lam_of_floor_le
    hn2 htpos hlam hg0 hq

#print axioms normalized_gap_lt_n_sub_one_mul_lam_of_floor_le
#print axioms normalized_gap_lt_n_sub_one_mul_lam_of_floor_le_sendov

end JSP000404Research
