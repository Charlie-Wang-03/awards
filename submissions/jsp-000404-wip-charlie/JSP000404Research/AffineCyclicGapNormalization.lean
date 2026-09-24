
import JSP000404Research.CyclicBandBudget
import JSP000404Research.ProjectiveGapCutRotation
import Mathlib.Tactic

/-!
# Affine normalization of one cyclic angular branch

Let theta lie on one unwrapped angular branch of circumference pi and set

  x = (theta-base)/lambda,

with Sendov normalization lambda=pi/t.

Translation by base does not change consecutive differences, and division by
lambda converts the angular circumference pi into the normalized circumference
t.

Hence for every nonempty angle list:

  cyclicRealGaps t (map x angles)
    = map (fun g => g/lambda) (projectiveGaps angles),

and after taking natural floors this is exactly

  cyclicBandQuotients t (map x angles)
    = quotientList t (normalizedProjectiveGaps angles).

Thus the centre quotient exponent and the integer unit-band arithmetic are
literally computed from the same cyclic gap data after affine normalization.
-/

namespace JSP000404Research

open Real

noncomputable def affineAngleValue
    (base lam theta : ℝ) : ℝ :=
  (theta - base) / lam

theorem sendov_pi_div_lam
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t) :
    Real.pi / lam = t := by
  rw [hlam]
  field_simp [Real.pi_ne_zero, ne_of_gt ht]

theorem sendov_scaled_normalized_gap
    {lam t g : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t) :
    t * (g / Real.pi) = g / lam := by
  rw [hlam]
  field_simp [Real.pi_ne_zero, ne_of_gt ht]
  ring

theorem getLastD_map_affineAngleValue
    (base lam a : ℝ) (xs : List ℝ) :
    (xs.map (affineAngleValue base lam)).getLastD
        (affineAngleValue base lam a)
      =
    affineAngleValue base lam (xs.getLastD a) := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.getLastD_cons, ih]

theorem successiveDiffsFrom_map_affineAngleValue
    (base lam a : ℝ) (xs : List ℝ)
    (hlam0 : lam ≠ 0) :
    successiveDiffsFrom
        (affineAngleValue base lam a)
        (xs.map (affineAngleValue base lam))
      =
    (successiveDiffsFrom a xs).map
      (fun g => g / lam) := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons x xs ih =>
      simp [successiveDiffsFrom, ih, affineAngleValue]
      field_simp [hlam0]
      ring

/-- Exact gap-list conversion under the Sendov affine normalization. -/
theorem cyclicRealGaps_map_affine_eq
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (base a : ℝ) (xs : List ℝ) :
    cyclicRealGaps t
        ((a :: xs).map
          (affineAngleValue base lam))
      =
    (projectiveGaps (a :: xs)).map
      (fun g => g / lam) := by
  have hlam0 : lam ≠ 0 := by
    rw [hlam]
    exact div_ne_zero Real.pi_ne_zero (ne_of_gt ht)
  have hscale :
      t = Real.pi / lam :=
    (sendov_pi_div_lam ht hlam).symm
  simp only [List.map_cons, cyclicRealGaps,
    projectiveGaps, List.map_append,
    List.map_singleton]
  rw [successiveDiffsFrom_map_affineAngleValue
      base lam a xs hlam0,
      getLastD_map_affineAngleValue]
  congr 1
  unfold affineAngleValue
  rw [hscale]
  field_simp [hlam0]
  ring

/-- Floors of the affine cyclic gaps are the original Sendov quotient list. -/
theorem cyclicBandQuotients_map_affine_eq_quotientList
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (base a : ℝ) (xs : List ℝ) :
    cyclicBandQuotients t
        ((a :: xs).map
          (affineAngleValue base lam))
      =
    quotientList t
      (normalizedProjectiveGaps (a :: xs)) := by
  unfold cyclicBandQuotients quotientList
  rw [cyclicRealGaps_map_affine_eq
      ht hlam base a xs]
  unfold normalizedProjectiveGaps
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro g hg
  simp only [Function.comp_apply]
  rw [sendov_scaled_normalized_gap ht hlam]

/-- Therefore the quotient exponent is exactly preserved by affine
normalization. -/
theorem listExponent_cyclicBandQuotients_affine
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (base a : ℝ) (xs : List ℝ) :
    listExponent
        (cyclicBandQuotients t
          ((a :: xs).map
            (affineAngleValue base lam)))
      =
    listExponent
        (quotientList t
          (normalizedProjectiveGaps (a :: xs))) := by
  rw [cyclicBandQuotients_map_affine_eq_quotientList
    ht hlam base a xs]

#print axioms sendov_pi_div_lam
#print axioms sendov_scaled_normalized_gap
#print axioms cyclicRealGaps_map_affine_eq
#print axioms cyclicBandQuotients_map_affine_eq_quotientList
#print axioms listExponent_cyclicBandQuotients_affine

end JSP000404Research
