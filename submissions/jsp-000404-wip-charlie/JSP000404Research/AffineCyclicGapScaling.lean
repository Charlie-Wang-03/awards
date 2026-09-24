
import JSP000404Research.LinearBandGapCapacity
import JSP000404Research.CentreQuotientData
import JSP000404Research.CyclicQuotientRotation
import Mathlib.Tactic

/-!
# Affine scaling of cyclic gap quotients

A uniform affine coordinate change

  x(theta) = (theta-shift)/lambda

sends a cyclic angle system of circumference pi to one of circumference
pi/lambda.

Successive differences scale by 1/lambda, and the cyclic wrap difference does
the same.  Hence the floor-gap quotient list after the affine change is exactly

  map (fun g => floor(g/lambda)) (projectiveGaps angles).

When t=pi/lambda this is also exactly

  quotientList t (normalizedProjectiveGaps angles),

because t*(g/pi)=g/lambda.

This module isolates the scaling algebra from the later projective-cut
rotation argument.
-/

namespace JSP000404Research

open Real

def affineAngleValue
    (shift lam theta : ℝ) : ℝ :=
  (theta - shift) / lam

theorem successiveDiffsFrom_affineAngleValue
    (shift lam a : ℝ) (xs : List ℝ) :
    successiveDiffsFrom (affineAngleValue shift lam a)
        (xs.map (affineAngleValue shift lam))
      =
    (successiveDiffsFrom a xs).map (fun g => g / lam) := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons b bs ih =>
      simp only [List.map_cons, successiveDiffsFrom, List.map_cons]
      constructor
      · unfold affineAngleValue
        ring
      · exact ih b

theorem getLastD_map_affineAngleValue
    (shift lam a : ℝ) (xs : List ℝ) :
    (xs.map (affineAngleValue shift lam)).getLastD
        (affineAngleValue shift lam a)
      =
    affineAngleValue shift lam (xs.getLastD a) := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons b bs ih =>
      rw [List.getLastD_cons, List.getLastD_cons]
      cases bs with
      | nil =>
          simp
      | cons c cs =>
          simpa using ih b (c :: cs)

theorem linearCyclicGapQuotients_affine_eq_projectiveGap_floors
    (shift lam a : ℝ) (xs : List ℝ) :
    linearCyclicGapQuotients (Real.pi / lam)
        ((a :: xs).map (affineAngleValue shift lam))
      =
    (projectiveGaps (a :: xs)).map
      (fun g => Nat.floor (g / lam)) := by
  simp only [List.map_cons, linearCyclicGapQuotients,
    projectiveGaps, List.map_append, List.map_singleton]
  rw [successiveDiffsFrom_affineAngleValue,
      List.map_map,
      getLastD_map_affineAngleValue]
  congr 2
  unfold affineAngleValue
  congr 1
  ring

theorem scaled_projectiveGap_floor_eq_quotient
    {t lam g : ℝ}
    (hlam : lam = Real.pi / t)
    (ht : 0 < t) :
    Nat.floor (g / lam) =
      Nat.floor (t * (g / Real.pi)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have ht0 : t ≠ 0 := ne_of_gt ht
  rw [hlam]
  congr 1
  field_simp [hpi, ht0]
  ring

theorem projectiveGap_floor_map_eq_quotientList
    (t lam : ℝ)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (angles : List ℝ) :
    (projectiveGaps angles).map
        (fun g => Nat.floor (g / lam))
      =
    quotientList t (normalizedProjectiveGaps angles) := by
  unfold quotientList normalizedProjectiveGaps
  rw [List.map_map]
  apply List.map_congr_left
  intro g hg
  exact scaled_projectiveGap_floor_eq_quotient
    (g := g) hlam ht

/-- Main quotient-list invariance under a uniform affine coordinate change. -/
theorem linearCyclicGapQuotients_affine_eq_quotientList
    (shift lam t : ℝ)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (angles : List ℝ) :
    linearCyclicGapQuotients t
        (angles.map (affineAngleValue shift lam))
      =
    quotientList t (normalizedProjectiveGaps angles) := by
  cases angles with
  | nil =>
      simp [linearCyclicGapQuotients, quotientList,
        normalizedProjectiveGaps, projectiveGaps]
  | cons a xs =>
      have htCirc : t = Real.pi / lam := by
        rw [hlam]
        field_simp [Real.pi_ne_zero, ne_of_gt ht]
      rw [htCirc]
      rw [linearCyclicGapQuotients_affine_eq_projectiveGap_floors]
      rw [projectiveGap_floor_map_eq_quotientList
        t lam ht hlam]
      rw [← htCirc]

/-- Exponent form. -/
theorem linearExponent_affine_eq_projectiveExponent
    (shift lam t : ℝ)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (angles : List ℝ) :
    listExponent
        (linearCyclicGapQuotients t
          (angles.map (affineAngleValue shift lam)))
      =
    listExponent
        (quotientList t (normalizedProjectiveGaps angles)) := by
  rw [linearCyclicGapQuotients_affine_eq_quotientList
    shift lam t ht hlam angles]

#print axioms successiveDiffsFrom_affineAngleValue
#print axioms linearCyclicGapQuotients_affine_eq_projectiveGap_floors
#print axioms projectiveGap_floor_map_eq_quotientList
#print axioms linearCyclicGapQuotients_affine_eq_quotientList
#print axioms linearExponent_affine_eq_projectiveExponent

end JSP000404Research
