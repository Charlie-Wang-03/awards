
import JSP000404Research.CanonicalRayReversal
import JSP000404Research.SignedRayAngle
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Canonical signs are rigid inside one projective unit band

Fix Sendov normalization

  lambda = pi / t,   t > 0.

For a canonical projective ray at centre i define its normalized line
coordinate

  x = t * theta / pi = theta / lambda.

If two rays lie in the same half-open unit band [m,m+1), then their
projective parameters differ by strictly less than lambda.

Under the global angle cap, opposite canonical signs would force a projective
parameter separation at least lambda.  Hence all rays incident to one centre
inside one unit band have the same canonical sign.

This makes the canonical sign a well-defined Boolean bit of a
centre/projective-band pair.
-/

namespace JSP000404Research

open Real

def normalizedRayTheta
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t : ℝ) (i : V) (j : OtherVertex i) : ℝ :=
  t * rayThetaAt hp i j / Real.pi

theorem normalizedRayTheta_eq_div_lam
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V) (j : OtherVertex i) :
    normalizedRayTheta hp t i j =
      rayThetaAt hp i j / lam := by
  unfold normalizedRayTheta
  rw [hlam]
  field_simp [ne_of_gt ht, Real.pi_ne_zero]
  ring

theorem normalizedRayTheta_nonneg
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} (ht : 0 ≤ t)
    (i : V) (j : OtherVertex i) :
    0 ≤ normalizedRayTheta hp t i j := by
  unfold normalizedRayTheta
  positivity

theorem normalizedRayTheta_lt_t
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} (ht : 0 < t)
    (i : V) (j : OtherVertex i) :
    normalizedRayTheta hp t i j < t := by
  unfold normalizedRayTheta
  have hj := rayThetaAt_lt_pi hp i j
  have hpi := Real.pi_pos
  nlinarith [rayThetaAt_nonneg hp i j]

/-- Two normalized coordinates in the same unit band differ by less than one. -/
theorem abs_sub_lt_one_of_same_unit_band
    {x y : ℝ} {m : ℕ}
    (hxm : (m : ℝ) ≤ x)
    (hxM : x < (m : ℝ) + 1)
    (hym : (m : ℝ) ≤ y)
    (hyM : y < (m : ℝ) + 1) :
    |x - y| < 1 := by
  rw [abs_lt]
  constructor <;> linarith

/-- Same normalized unit band implies projective parameter separation
strictly below lambda. -/
theorem rayTheta_abs_sub_lt_lam_of_same_band
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V) (j k : OtherVertex i)
    {m : ℕ}
    (hjm : (m : ℝ) ≤ normalizedRayTheta hp t i j)
    (hjM : normalizedRayTheta hp t i j < (m : ℝ) + 1)
    (hkm : (m : ℝ) ≤ normalizedRayTheta hp t i k)
    (hkM : normalizedRayTheta hp t i k < (m : ℝ) + 1) :
    |rayThetaAt hp i j - rayThetaAt hp i k| < lam := by
  have hlamPos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos ht
  have hnorm :=
    abs_sub_lt_one_of_same_unit_band
      hjm hjM hkm hkM
  rw [normalizedRayTheta_eq_div_lam
        hp ht hlam i j,
      normalizedRayTheta_eq_div_lam
        hp ht hlam i k] at hnorm
  have hdiv :
      |(rayThetaAt hp i j - rayThetaAt hp i k) / lam| < 1 := by
    have h :
        rayThetaAt hp i j / lam -
            rayThetaAt hp i k / lam
          =
        (rayThetaAt hp i j - rayThetaAt hp i k) / lam := by
      ring
    rw [h] at hnorm
    exact hnorm
  rw [abs_div, abs_of_pos hlamPos] at hdiv
  exact (div_lt_one hlamPos).1 hdiv

/-- Main sign-rigidity theorem for one projective unit band. -/
theorem raySignAt_eq_of_same_projective_band
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V) (j k : OtherVertex i)
    (hjk : j ≠ k)
    {m : ℕ}
    (hjm : (m : ℝ) ≤ normalizedRayTheta hp t i j)
    (hjM : normalizedRayTheta hp t i j < (m : ℝ) + 1)
    (hkm : (m : ℝ) ≤ normalizedRayTheta hp t i k)
    (hkM : normalizedRayTheta hp t i k < (m : ℝ) + 1) :
    raySignAt hp i j = raySignAt hp i k := by
  by_contra hsign
  have hsmall :=
    rayTheta_abs_sub_lt_lam_of_same_band
      hp ht hlam i j k hjm hjM hkm hkM
  have hj0 := rayThetaAt_nonneg hp i j
  have hk0 := rayThetaAt_nonneg hp i k
  have hjpi := rayThetaAt_lt_pi hp i j
  have hkpi := rayThetaAt_lt_pi hp i k
  have hspanJK :
      rayThetaAt hp i k - rayThetaAt hp i j ≤ Real.pi := by
    linarith
  have hspanKJ :
      rayThetaAt hp i j - rayThetaAt hp i k ≤ Real.pi := by
    linarith
  have hji : j.1 ≠ i := j.2
  have hki : k.1 ≠ i := k.2
  have hjkVal : j.1 ≠ k.1 := by
    intro h
    apply hjk
    exact Subtype.ext h
  have hcapJK :
      EuclideanGeometry.angle (p j.1) (p i) (p k.1)
        ≤ Real.pi - lam :=
    hcap j.1 i k.1 hji hki.symm hjkVal
  change
    InnerProductGeometry.angle
        (p j.1 - p i) (p k.1 - p i)
      ≤ Real.pi - lam at hcapJK
  rw [rayRepAt_eq hp i j, rayRepAt_eq hp i k,
      angle_positive_smul_signedRay
        (rayRhoAt_pos hp i j)
        (rayRhoAt_pos hp i k)] at hcapJK
  rcases le_total (rayThetaAt hp i j) (rayThetaAt hp i k) with horder | horder
  · have hgap :=
      lam_le_parameter_gap_of_opposite_signs
        (rayRhoAt_pos hp i j)
        (rayRhoAt_pos hp i k)
        horder hspanJK hsign hcapJK
    have habs :
        |rayThetaAt hp i j - rayThetaAt hp i k| =
          rayThetaAt hp i k - rayThetaAt hp i j := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    rw [habs] at hsmall
    linarith
  · have hsign' :
        raySignAt hp i k ≠ raySignAt hp i j := by
      exact Ne.symm hsign
    have hcapKJ :
        InnerProductGeometry.angle
            (rayRhoAt hp i k •
              signedRayDirection
                (raySignAt hp i k)
                (rayThetaAt hp i k))
            (rayRhoAt hp i j •
              signedRayDirection
                (raySignAt hp i j)
                (rayThetaAt hp i j))
          ≤ Real.pi - lam := by
      simpa [InnerProductGeometry.angle_comm] using hcapJK
    have hgap :=
      lam_le_parameter_gap_of_opposite_signs
        (rayRhoAt_pos hp i k)
        (rayRhoAt_pos hp i j)
        horder hspanKJ hsign' hcapKJ
    have habs :
        |rayThetaAt hp i j - rayThetaAt hp i k| =
          rayThetaAt hp i j - rayThetaAt hp i k := by
      rw [abs_of_nonneg]
      linarith
    rw [habs] at hsmall
    linarith

#print axioms normalizedRayTheta_eq_div_lam
#print axioms rayTheta_abs_sub_lt_lam_of_same_band
#print axioms raySignAt_eq_of_same_projective_band

end JSP000404Research
