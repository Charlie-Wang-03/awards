import JSP000404Research.FourCentreMixedInteriorContradiction
import Mathlib.Tactic

/-!
# Strong hidden-angle reduction to the kernel-checked weakened interior terminal

The original interface requires (n-1)*lambda <= angle(s,b,c).
Since delta >= 0 and lambda > 0, this implies
((n-1)-delta)*lambda <= angle(s,b,c), which is precisely the input
of the geometric interior arithmetic contradiction.

This reuses the verified geometry rather than duplicating the triangle
angle-splitting proof and preserves the original theorem statement.
-/

namespace JSP000404Research

open Real

theorem no_mixed_fourth_inside_of_hidden_angle_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hinside :
      p c ∈ convexHull ℝ ({p s, p a, p b} : Set Plane))
    (hhidden :
      ((n - 1 : ℕ) : ℝ) * lam ≤
        EuclideanGeometry.angle (p s) (p b) (p c)) :
    False := by
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hweak :
      (((n - 1 : ℕ) : ℝ) - delta) * lam ≤
        EuclideanGeometry.angle (p s) (p b) (p c) := by
    have hnonneg : 0 ≤ delta * lam :=
      mul_nonneg hdelta0 (le_of_lt hlampos)
    nlinarith
  exact no_mixed_fourth_inside_of_weakened_hidden_angle_fin_four
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc hinside hweak

#print axioms no_mixed_fourth_inside_of_hidden_angle_fin_four

end JSP000404Research
