import JSP000404Research.DeficitTwoThreeRayZeroGap
import JSP000404Research.SmallSameSignGapAngle
import JSP000404Research.CanonicalSignGap
import Mathlib.Tactic

/-!
# The unique zero gap is a genuinely delta-small angle

In a four-point deficit-two/support-two centre, any zero quotient gap has
scaled projective width at most delta.

A zero quotient cannot be a sign-transition gap: CanonicalSignGap says every
actual sign change carries positive quotient.  Hence ordinary zero gaps have
equal canonical signs, while a zero wrap gap satisfies the corresponding
lifted same-sign relation.

SmallSameSignGapAngle then converts the projective estimate into a genuine
Euclidean triangle-angle estimate <= delta*lambda.
-/

namespace JSP000404Research

open Real

theorem zero_q01_actual_angle_le_delta_lam
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (hcap : AngleCap p lam)
    {t delta lam : ℝ} {n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (hq0 : Nat.floor (t * gap01 r0 r1) = 0) :
    EuclideanGeometry.angle (p r0.1) (p i) (p r1.1) ≤
      delta * lam := by
  have hsmall :=
    (zero_gap_scaled_le_delta_of_deficit_two_support_two
      C ht htpos.le r0 r1 r2 hrays hexp hsupport).1 hq0
  have hord := (three_ray_theta_order C r0 r1 r2 hrays).1
  have hr01 : r0 ≠ r1 := by
    intro h
    have hn := C.nodup
    rw [hrays] at hn
    simp [h] at hn
  have hsign : raySignAt hp i r0 = raySignAt hp i r1 := by
    by_contra hne
    have hnonzero :=
      floor_t_mul_gap_ne_zero_of_canonical_sign_ne
        hp hcap htpos hlam i hr01 hord hne
    apply hnonzero
    simpa [gap01] using hq0
  exact actual_angle_le_delta_lam_of_ordinary_same_sign_gap
    hp htpos hlam i hord hsign
    (by simpa [gap01] using hsmall)

theorem zero_q12_actual_angle_le_delta_lam
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (hcap : AngleCap p lam)
    {t delta lam : ℝ} {n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (hq1 : Nat.floor (t * gap12 r1 r2) = 0) :
    EuclideanGeometry.angle (p r1.1) (p i) (p r2.1) ≤
      delta * lam := by
  have hsmall :=
    (zero_gap_scaled_le_delta_of_deficit_two_support_two
      C ht htpos.le r0 r1 r2 hrays hexp hsupport).2.1 hq1
  have hord := (three_ray_theta_order C r0 r1 r2 hrays).2
  have hr12 : r1 ≠ r2 := by
    intro h
    have hn := C.nodup
    rw [hrays] at hn
    simp [h] at hn
  have hsign : raySignAt hp i r1 = raySignAt hp i r2 := by
    by_contra hne
    have hnonzero :=
      floor_t_mul_gap_ne_zero_of_canonical_sign_ne
        hp hcap htpos hlam i hr12 hord hne
    apply hnonzero
    simpa [gap12] using hq1
  exact actual_angle_le_delta_lam_of_ordinary_same_sign_gap
    hp htpos hlam i hord hsign
    (by simpa [gap12] using hsmall)

theorem zero_q20_actual_angle_le_delta_lam
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (hcap : AngleCap p lam)
    {t delta lam : ℝ} {n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (hq2 : Nat.floor (t * gap20 r0 r2) = 0) :
    EuclideanGeometry.angle (p r2.1) (p i) (p r0.1) ≤
      delta * lam := by
  have hsmall :=
    (zero_gap_scaled_le_delta_of_deficit_two_support_two
      C ht htpos.le r0 r1 r2 hrays hexp hsupport).2.2 hq2
  have hord :
      rayThetaAt hp i r0 ≤ rayThetaAt hp i r2 :=
    (three_ray_theta_order C r0 r1 r2 hrays).1.trans
      (three_ray_theta_order C r0 r1 r2 hrays).2
  have hr02 : r0 ≠ r2 := by
    intro h
    have hn := C.nodup
    rw [hrays] at hn
    simp [h] at hn
  have hsign :
      raySignAt hp i r2 = !raySignAt hp i r0 := by
    by_contra hne
    have hnonzero :=
      floor_t_mul_wrap_gap_ne_zero_of_canonical_sign_ne
        hp hcap htpos hlam i hr02.symm hord hne
    apply hnonzero
    simpa [gap20] using hq2
  exact actual_angle_le_delta_lam_of_wrap_same_sign_gap
    hp htpos hlam i hord hsign
    (by simpa [gap20] using hsmall)

#print axioms zero_q01_actual_angle_le_delta_lam
#print axioms zero_q12_actual_angle_le_delta_lam
#print axioms zero_q20_actual_angle_le_delta_lam

end JSP000404Research
