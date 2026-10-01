import JSP000404Research.ExactTwoSupportOnePairExclusion
import JSP000404Research.ProjectionQTTTSmallPair
import Mathlib.Tactic

/-!
# Exact-two support small angles form a perfect crossed matching

Let o1,o2 be the two support-one second-layer centres and s1,s2 the two
support-two second-layer centres.

At s1 the generic support-two small-pair theorem gives one small pair among
{o1,o2,s2}.  The pair {o1,o2} is impossible by the support-one pair exclusion,
so the small angle uses s2 and exactly one support-one centre.  Likewise at s2.

The two support-two centres cannot choose the same support-one centre.  If they
did, the triangle formed by that support-one centre and s1,s2 would have angle
bounds

  (1+delta)*lambda, delta*lambda, delta*lambda,

whose coefficient sum 1+3*delta is strictly below t=n+delta for n>=3 and
delta<1/2.  Hence the choices are opposite and form a perfect matching.
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
    have hmul :=
      mul_lt_mul_of_pos_right hcoeff hlampos
    rw [hpiEq] at hmul
    exact hmul
  have htri :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p s₁) (p₂ := p o) (p s₂)
      (hp.ne hos1)
  have hs2' :
      EuclideanGeometry.angle (p s₁) (p s₂) (p o)
        ≤ delta * lam := by
    simpa [EuclideanGeometry.angle_comm] using hs2
  nlinarith

def ExactTwoCrossedSupportMatching
    {V : Type*}
    (p : V → Plane) (delta lam : ℝ)
    (o₁ o₂ s₁ s₂ : V) : Prop :=
  (
    EuclideanGeometry.angle (p o₁) (p s₁) (p s₂)
      ≤ delta * lam ∧
    EuclideanGeometry.angle (p o₂) (p s₂) (p s₁)
      ≤ delta * lam
  )
  ∨
  (
    EuclideanGeometry.angle (p o₂) (p s₁) (p s₂)
      ≤ delta * lam ∧
    EuclideanGeometry.angle (p o₁) (p s₂) (p s₁)
      ≤ delta * lam
  )

theorem exactTwo_support_small_angles_perfect_crossed_matching
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {o₁ o₂ s₁ s₂ : V}
    (ho12 : o₁ ≠ o₂)
    (ho1s1 : o₁ ≠ s₁)
    (ho1s2 : o₁ ≠ s₂)
    (ho2s1 : o₂ ≠ s₁)
    (ho2s2 : o₂ ≠ s₂)
    (hs12 : s₁ ≠ s₂)
    (Co₁ : CentreProjectiveCycle hp o₁)
    (Co₂ : CentreProjectiveCycle hp o₂)
    (Cs₁ : CentreProjectiveCycle hp s₁)
    (Cs₂ : CentreProjectiveCycle hp s₂)
    (ho1Second : centreExponent Co₁ t = n - 2)
    (ho2Second : centreExponent Co₂ t = n - 2)
    (hs1Second : centreExponent Cs₁ t = n - 2)
    (hs2Second : centreExponent Cs₂ t = n - 2)
    (ho1Support :
      positiveSupport (centreQuotient Co₁ t) = 1)
    (ho2Support :
      positiveSupport (centreQuotient Co₂ t) = 1)
    (hs1Support :
      positiveSupport (centreQuotient Cs₁ t) = 2)
    (hs2Support :
      positiveSupport (centreQuotient Cs₂ t) = 2)
    (Ho₁ : HighExponentTransitionIntervalCertificate hp t o₁ Co₁)
    (Ho₂ : HighExponentTransitionIntervalCertificate hp t o₂ Co₂) :
    ExactTwoCrossedSupportMatching p delta lam o₁ o₂ s₁ s₂ := by
  have hs1Small :
      SmallPairAmongOtherThree p delta lam s₁ o₁ o₂ s₂ :=
    secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      ho1s1.symm ho2s1.symm hs12
      ho12 ho1s2 ho2s2
      Cs₁ hs1Second hs1Support

  have hs2Small :
      SmallPairAmongOtherThree p delta lam s₂ o₁ o₂ s₁ :=
    secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      ho1s2.symm ho2s2.symm hs12.symm
      ho12 ho1s1 ho2s1
      Cs₂ hs2Second hs2Support

  have hnotO12atS1 :
      ¬ EuclideanGeometry.angle (p o₁) (p s₁) (p o₂)
          ≤ delta * lam := by
    intro hsmall
    exact supportTwo_small_pair_not_two_supportOne_centres
      hp hn3 hdelta0 hdeltaHalf ht hlam
      ho12 ho1s1 ho2s1
      Co₁ Co₂ ho1Second ho2Second
      ho1Support ho2Support Ho₁ Ho₂ hsmall

  have hnotO12atS2 :
      ¬ EuclideanGeometry.angle (p o₁) (p s₂) (p o₂)
          ≤ delta * lam := by
    intro hsmall
    exact supportTwo_small_pair_not_two_supportOne_centres
      hp hn3 hdelta0 hdeltaHalf ht hlam
      ho12 ho1s2 ho2s2
      Co₁ Co₂ ho1Second ho2Second
      ho1Support ho2Support Ho₁ Ho₂ hsmall

  unfold SmallPairAmongOtherThree at hs1Small hs2Small
  rcases hs1Small with hs1O12 | hs1O1 | hs1O2
  · exact False.elim (hnotO12atS1 hs1O12)
  · rcases hs2Small with hs2O12 | hs2O1 | hs2O2
    · exact False.elim (hnotO12atS2 hs2O12)
    · have hoAngle :=
        secondLayer_supportOne_all_angles_le_one_add_delta_lam
          hp hn3 hdelta0 ht hlam
          Co₁ ho1Second ho1Support Ho₁
          ho1s1 ho1s2
      exact False.elim
        (impossible_one_supportOne_bound_and_two_delta_angles
          hp hn3 hdelta0 hdeltaHalf ht hlam
          ho1s1 ho1s2 hs12
          hoAngle hs1O1
          (by simpa [EuclideanGeometry.angle_comm] using hs2O1))
    · exact Or.inl
        ⟨hs1O1,
          by simpa [EuclideanGeometry.angle_comm] using hs2O2⟩
  · rcases hs2Small with hs2O12 | hs2O1 | hs2O2
    · exact False.elim (hnotO12atS2 hs2O12)
    · exact Or.inr
        ⟨hs1O2,
          by simpa [EuclideanGeometry.angle_comm] using hs2O1⟩
    · have hoAngle :=
        secondLayer_supportOne_all_angles_le_one_add_delta_lam
          hp hn3 hdelta0 ht hlam
          Co₂ ho2Second ho2Support Ho₂
          ho2s1 ho2s2
      exact False.elim
        (impossible_one_supportOne_bound_and_two_delta_angles
          hp hn3 hdelta0 hdeltaHalf ht hlam
          ho2s1 ho2s2 hs12
          hoAngle
          (by simpa [EuclideanGeometry.angle_comm] using hs1O2)
          (by simpa [EuclideanGeometry.angle_comm] using hs2O2))

#print axioms impossible_one_supportOne_bound_and_two_delta_angles
#print axioms exactTwo_support_small_angles_perfect_crossed_matching

end JSP000404Research
