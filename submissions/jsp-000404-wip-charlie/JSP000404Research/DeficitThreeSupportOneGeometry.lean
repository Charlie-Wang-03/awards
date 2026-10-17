import JSP000404Research.ConcreteOneSupportInterval
import JSP000404Research.ConcreteDeficitThree
import JSP000404Research.SharpCentre
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Geometry of a deficit-three / support-one centre

For an exact n-3 centre with quotient support one, the unique positive
transition quotient is n-2.  Its complementary common-signed interval
therefore has width at most

  (2+delta)*lambda.

Hence every genuine angle at that centre has the same upper bound.

If s is a top sharp centre, triangle s-a-b then forces the angle at every
third vertex b between the rays to s and a to satisfy

  (n-2-delta)*lambda <= angle(s,b,a).

For n>=4 and delta<1/2 this lower bound is strictly larger than
(1+delta)*lambda, the complete zero-angle budget of a deficit-three/support-two
centre.
-/

namespace JSP000404Research

open Real

theorem deficit_three_support_one_all_angles_le
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a : V}
    (Ca : CentreProjectiveCycle hp a)
    (hA : centreExponent Ca t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1) :
    ∀ j k,
      j ≠ a → k ≠ a → j ≠ k →
      EuclideanGeometry.angle (p j) (p a) (p k) ≤
        (2 + delta) * lam := by
  obtain ⟨qe, ge, low, width, sigma, hqe0, hqeExp,
      hqeLe, hgePos, hwidthEq, hwidthNonneg, hwidthLtPi, hrepr⟩ :=
    concrete_one_support_interval_certificate
      hp hcap (by omega : 1 ≤ n) hdelta0 ht hlam a Ca hsupA
  have hqe : qe = n - 2 := by
    rw [hqeExp, hA]
    omega
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hge :
      ((n - 2 : ℕ) : ℝ) / t ≤ ge := by
    rw [div_le_iff₀ htpos]
    rw [← hqe]
    simpa only [mul_comm] using hqeLe
  have hncast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    simpa only [Nat.cast_ofNat] using
      (Nat.cast_sub (by omega : 2 ≤ n) :
        ((n - 2 : ℕ) : ℝ) = (n : ℝ) - ((2 : ℕ) : ℝ))
  have hwidth :
      width ≤ (2 + delta) * lam := by
    rw [hwidthEq, hlam]
    rw [hncast] at hge
    have hpi := Real.pi_pos
    have htEq : (n : ℝ) - 2 = t - (2 + delta) := by
      rw [ht]
      ring
    rw [htEq] at hge
    have hbound :
        1 - ge ≤ (2 + delta) / t := by
      rw [div_eq_mul_inv] at hge ⊢
      have htinv : 0 < 1 / t := one_div_pos.mpr htpos
      have hone :
          1 - (t - (2 + delta)) * t⁻¹ =
            (2 + delta) * t⁻¹ := by
        field_simp [ne_of_gt htpos]
        ring
      rw [← hone]
      linarith
    have hmul :=
      mul_le_mul_of_nonneg_left hbound Real.pi_pos.le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  intro j k hja hka hjk
  obtain ⟨rhoJ, thetaJ, hrhoJ, hJlo, hJhi, hJrepr⟩ :=
    hrepr j hja
  obtain ⟨rhoK, thetaK, hrhoK, hKlo, hKhi, hKrepr⟩ :=
    hrepr k hka
  have htheta : |thetaJ - thetaK| ≤ width := by
    rcases le_total thetaJ thetaK with hJK | hKJ
    · rw [abs_of_nonpos (sub_nonpos.mpr hJK)]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hKJ)]
      linarith
  have hdiff : |thetaJ - thetaK| ≤ Real.pi :=
    htheta.trans hwidthLtPi.le
  have hangle :
      EuclideanGeometry.angle (p j) (p a) (p k) ≤ width := by
    change InnerProductGeometry.angle
      (p j - p a) (p k - p a) ≤ width
    rw [hJrepr, hKrepr,
      angle_positive_smul_signedRay hrhoJ hrhoK
        sigma sigma thetaJ thetaK,
      angle_signedRayDirection_eq_of_sign_eq rfl hdiff]
    exact htheta
  exact hangle.trans hwidth

theorem sharp_and_deficit_three_support_one_force_large_outer_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hs : SharpAt p delta lam s)
    (Ca : CentreProjectiveCycle hp a)
    (hA : centreExponent Ca t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1) :
    (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
      EuclideanGeometry.angle (p s) (p b) (p a) := by
  have hS :
      EuclideanGeometry.angle (p a) (p s) (p b) ≤
        delta * lam :=
    hs a b hsa.symm hsb.symm hab
  have hAang :
      EuclideanGeometry.angle (p s) (p a) (p b) ≤
        (2 + delta) * lam :=
    deficit_three_support_one_all_angles_le
      hp hcap hn hdelta0 ht hlam
      Ca hA hsupA s b hsa hab.symm hsb
  have hsum :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p a) (p₂ := p s) (p b)
      (hp.ne hsa)
  have hcomm :
      EuclideanGeometry.angle (p b) (p a) (p s) =
        EuclideanGeometry.angle (p s) (p a) (p b) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcomm] at hsum
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  have hncast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    simpa only [Nat.cast_ofNat] using
      (Nat.cast_sub (by omega : 2 ≤ n) :
        ((n - 2 : ℕ) : ℝ) = (n : ℝ) - ((2 : ℕ) : ℝ))
  rw [hpi, ht] at hsum
  rw [hncast]
  nlinarith

theorem one_add_delta_lam_lt_large_outer
    {delta lam : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam) :
    (1 + delta) * lam <
      (((n - 2 : ℕ) : ℝ) - delta) * lam := by
  have hncast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    simpa only [Nat.cast_ofNat] using
      (Nat.cast_sub (by omega : 2 ≤ n) :
        ((n - 2 : ℕ) : ℝ) = (n : ℝ) - ((2 : ℕ) : ℝ))
  rw [hncast]
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

#print axioms deficit_three_support_one_all_angles_le
#print axioms sharp_and_deficit_three_support_one_force_large_outer_angle
#print axioms one_add_delta_lam_lt_large_outer

end JSP000404Research
