import JSP000404Research.CutProjectiveBandPartition
import Mathlib.Tactic

/-!
# Genuine small angles inside one arbitrary cut band

For a projective cut c, two distinct incident rays in the same normalized unit
band have cut coordinates differing by less than one.  Under lambda=pi/t this
means their cut parameters differ by less than lambda.

The global angle cap forces their adjusted cut signs to agree.  Therefore the
actual Euclidean angle is the ordinary parameter difference, not the
supplementary branch, and is strictly less than lambda.
-/

namespace JSP000404Research

open Real

theorem cutRayTheta_abs_sub_lt_lam_of_same_band
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V) (j k : OtherVertex i)
    {m : ℕ}
    (hjm : (m : ℝ) ≤ cutNormalizedRayTheta hp t c i j)
    (hjM : cutNormalizedRayTheta hp t c i j < (m : ℝ) + 1)
    (hkm : (m : ℝ) ≤ cutNormalizedRayTheta hp t c i k)
    (hkM : cutNormalizedRayTheta hp t c i k < (m : ℝ) + 1) :
    |cutRayTheta hp c i j - cutRayTheta hp c i k| < lam := by
  have hlamPos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos ht
  have hnorm :=
    abs_sub_lt_one_of_same_unit_band
      hjm hjM hkm hkM
  rw [cutNormalizedRayTheta_eq_div_lam hp ht hlam i j,
      cutNormalizedRayTheta_eq_div_lam hp ht hlam i k] at hnorm
  have hdiv :
      |(cutRayTheta hp c i j -
          cutRayTheta hp c i k) / lam| < 1 := by
    have h :
        cutRayTheta hp c i j / lam -
            cutRayTheta hp c i k / lam =
          (cutRayTheta hp c i j -
            cutRayTheta hp c i k) / lam := by
      ring
    rw [h] at hnorm
    exact hnorm
  rw [abs_div, abs_of_pos hlamPos] at hdiv
  exact (div_lt_one hlamPos).1 hdiv

theorem actual_angle_lt_lam_of_same_cut_band
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) (j k : OtherVertex i)
    (hjk : j ≠ k)
    {m : ℕ}
    (hjm : (m : ℝ) ≤ cutNormalizedRayTheta hp t c i j)
    (hjM : cutNormalizedRayTheta hp t c i j < (m : ℝ) + 1)
    (hkm : (m : ℝ) ≤ cutNormalizedRayTheta hp t c i k)
    (hkM : cutNormalizedRayTheta hp t c i k < (m : ℝ) + 1) :
    EuclideanGeometry.angle (p j.1) (p i) (p k.1) < lam := by
  have hsign :
      cutRaySign hp c i j = cutRaySign hp c i k :=
    cutRaySign_eq_of_same_band
      hp hcap ht hlam hc0 hcpi i j k hjk
      hjm hjM hkm hkM
  have hsmall :
      |cutRayTheta hp c i j -
          cutRayTheta hp c i k| < lam :=
    cutRayTheta_abs_sub_lt_lam_of_same_band
      hp ht hlam i j k hjm hjM hkm hkM
  have hdiff :
      |(c + cutRayTheta hp c i j) -
          (c + cutRayTheta hp c i k)| ≤ Real.pi := by
    have hj0 := cutRayTheta_nonneg hp hc0 hcpi i j
    have hk0 := cutRayTheta_nonneg hp hc0 hcpi i k
    have hjpi := cutRayTheta_lt_pi hp hc0 hcpi i j
    have hkpi := cutRayTheta_lt_pi hp hc0 hcpi i k
    rw [show
      (c + cutRayTheta hp c i j) -
          (c + cutRayTheta hp c i k) =
        cutRayTheta hp c i j -
          cutRayTheta hp c i k by ring]
    rw [abs_le]
    constructor <;> linarith
  change
    InnerProductGeometry.angle
      (p j.1 - p i) (p k.1 - p i) < lam
  rw [cutRayRepAt_eq hp c i j,
      cutRayRepAt_eq hp c i k,
      angle_positive_smul_signedRay
        (rayRhoAt_pos hp i j)
        (rayRhoAt_pos hp i k),
      angle_signedRayDirection_eq_of_sign_eq hsign hdiff]
  simpa only [add_sub_add_left_eq_sub] using hsmall

#print axioms cutRayTheta_abs_sub_lt_lam_of_same_band
#print axioms actual_angle_lt_lam_of_same_cut_band

end JSP000404Research
