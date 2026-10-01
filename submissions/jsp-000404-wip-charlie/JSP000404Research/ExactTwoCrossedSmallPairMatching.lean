import JSP000404Research.ExactTwoSupportOnePairExclusion
import Mathlib.Tactic

/-!
# Exact-two small-pair matching reduces to two crossed patterns

Let o1,o2 be the two support-one centres and s1,s2 the two support-two
centres.

At each support-two centre, the three-marked small-pair theorem gives one of
three pairs among the other vertices.  The pair {o1,o2} is impossible by the
support-one narrow-cone triangle exclusion.

Thus each support-two centre must choose the other support-two centre together
with one support-one centre.  They cannot both choose the same support-one
centre: then triangle s1-s2-oi has two delta*lambda-small angles and the
support-one angle at oi is at most (1+delta)*lambda, whose coefficient sum
1+3delta is strictly below t=n+delta.

Therefore only the two crossed matchings remain.
-/

namespace JSP000404Research

theorem coeff_one_supportOne_plus_two_delta_lt_t
    {n : ℕ} {delta t : ℝ}
    (hn3 : 3 ≤ n)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta) :
    (1 + delta) + 2 * delta < t := by
  rw [ht]
  push_cast
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  linarith

theorem impossible_one_supportOne_bound_and_two_delta_angles
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {o s₁ s₂ : V}
    (hos1 : o ≠ s₁)
    (hos2 : o ≠ s₂)
    (hs12 : s₁ ≠ s₂)
    (ho :
      EuclideanGeometry.angle (p s₁) (p o) (p s₂)
        ≤ (1 + delta) * lam)
    (hs1 :
      EuclideanGeometry.angle (p o) (p s₁) (p s₂)
        ≤ delta * lam)
    (hs2 :
      EuclideanGeometry.angle (p o) (p s₂) (p s₁)
        ≤ delta * lam) :
    False := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hcoeff :=
    coeff_one_supportOne_plus_two_delta_lt_t
      hn3 hdeltaHalf ht
  have hpiEq : t * lam = Real.pi := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  have hsumLt :
      ((1 + delta) + 2 * delta) * lam < Real.pi := by
    have hmul := mul_lt_mul_of_pos_right hcoeff hlampos
    rw [hpiEq] at hmul
    exact hmul
  have htri :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p s₁) (p₂ := p o) (p s₂)
      (hp.ne hos1.symm)
  have hcommO :
      EuclideanGeometry.angle (p s₂) (p o) (p s₁) =
        EuclideanGeometry.angle (p s₁) (p o) (p s₂) :=
    EuclideanGeometry.angle_comm _ _ _
  have hcommS2 :
      EuclideanGeometry.angle (p s₁) (p s₂) (p o) =
        EuclideanGeometry.angle (p o) (p s₂) (p s₁) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommO,hcommS2] at htri
  nlinarith

theorem exactTwo_small_pairs_crossed_of_supportOne_cones
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {o₁ o₂ s₁ s₂ : V}
    (ho12 : o₁ ≠ o₂)
    (ho1s1 : o₁ ≠ s₁) (ho1s2 : o₁ ≠ s₂)
    (ho2s1 : o₂ ≠ s₁) (ho2s2 : o₂ ≠ s₂)
    (hs12 : s₁ ≠ s₂)
    (Co1 : CentreProjectiveCycle hp o₁)
    (Co2 : CentreProjectiveCycle hp o₂)
    (ho1Exp : centreExponent Co1 t = n - 2)
    (ho2Exp : centreExponent Co2 t = n - 2)
    (ho1Support :
      positiveSupport (centreQuotient Co1 t) = 1)
    (ho2Support :
      positiveSupport (centreQuotient Co2 t) = 1)
    (Ho1 : HighExponentTransitionIntervalCertificate hp t o₁ Co1)
    (Ho2 : HighExponentTransitionIntervalCertificate hp t o₂ Co2)
    (hs1Choices :
      EuclideanGeometry.angle (p o₁) (p s₁) (p o₂)
          ≤ delta * lam
      ∨
      EuclideanGeometry.angle (p o₂) (p s₁) (p s₂)
          ≤ delta * lam
      ∨
      EuclideanGeometry.angle (p s₂) (p s₁) (p o₁)
          ≤ delta * lam)
    (hs2Choices :
      EuclideanGeometry.angle (p o₁) (p s₂) (p o₂)
          ≤ delta * lam
      ∨
      EuclideanGeometry.angle (p o₂) (p s₂) (p s₁)
          ≤ delta * lam
      ∨
      EuclideanGeometry.angle (p s₁) (p s₂) (p o₁)
          ≤ delta * lam) :
    (
      EuclideanGeometry.angle (p s₂) (p s₁) (p o₁)
          ≤ delta * lam
      ∧
      EuclideanGeometry.angle (p o₂) (p s₂) (p s₁)
          ≤ delta * lam
    )
    ∨
    (
      EuclideanGeometry.angle (p o₂) (p s₁) (p s₂)
          ≤ delta * lam
      ∧
      EuclideanGeometry.angle (p s₁) (p s₂) (p o₁)
          ≤ delta * lam
    ) := by
  have hs1NotOO :
      ¬ EuclideanGeometry.angle (p o₁) (p s₁) (p o₂)
          ≤ delta * lam := by
    intro h
    exact supportTwo_small_pair_not_two_supportOne_centres
      hp hn3 hdelta0 hdeltaHalf ht hlam
      ho12 ho1s1 ho2s1
      Co1 Co2 ho1Exp ho2Exp
      ho1Support ho2Support Ho1 Ho2 h
  have hs2NotOO :
      ¬ EuclideanGeometry.angle (p o₁) (p s₂) (p o₂)
          ≤ delta * lam := by
    intro h
    exact supportTwo_small_pair_not_two_supportOne_centres
      hp hn3 hdelta0 hdeltaHalf ht hlam
      ho12 ho1s2 ho2s2
      Co1 Co2 ho1Exp ho2Exp
      ho1Support ho2Support Ho1 Ho2 h

  rcases hs1Choices with hs1OO | hs1O2 | hs1O1
  · exact False.elim (hs1NotOO hs1OO)
  · rcases hs2Choices with hs2OO | hs2O2 | hs2O1
    · exact False.elim (hs2NotOO hs2OO)
    · have ho2Angle :=
        secondLayer_supportOne_all_angles_le_one_add_delta_lam
          hp hn3 hdelta0 ht hlam
          Co2 ho2Exp ho2Support Ho2
          ho2s1.symm ho2s2.symm
      exact False.elim
        (impossible_one_supportOne_bound_and_two_delta_angles
          hp hn3 hdelta0 hdeltaHalf ht hlam
          ho2s1 ho2s2 hs12
          ho2Angle hs1O2 hs2O2)
    · exact Or.inr ⟨hs1O2,hs2O1⟩
  · rcases hs2Choices with hs2OO | hs2O2 | hs2O1
    · exact False.elim (hs2NotOO hs2OO)
    · exact Or.inl ⟨hs1O1,hs2O2⟩
    · have ho1Angle :=
        secondLayer_supportOne_all_angles_le_one_add_delta_lam
          hp hn3 hdelta0 ht hlam
          Co1 ho1Exp ho1Support Ho1
          ho1s1.symm ho1s2.symm
      exact False.elim
        (impossible_one_supportOne_bound_and_two_delta_angles
          hp hn3 hdelta0 hdeltaHalf ht hlam
          ho1s1 ho1s2 hs12
          ho1Angle
          (by simpa [EuclideanGeometry.angle_comm] using hs1O1)
          (by simpa [EuclideanGeometry.angle_comm] using hs2O1))

#print axioms coeff_one_supportOne_plus_two_delta_lt_t
#print axioms impossible_one_supportOne_bound_and_two_delta_angles
#print axioms exactTwo_small_pairs_crossed_of_supportOne_cones

end JSP000404Research
