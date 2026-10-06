import JSP000404Research.ProjectiveInterval
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

/-!
# Lightweight complex coordinates for the Euclidean plane

This module isolates the real-linear isometric identification

  Plane ≃ₗᵢ[ℝ] ℂ

and its interaction with the projective ray directions.  It is intentionally
kept below the canonical-projective-ray construction so generic-projection
half-plane geometry can use complex coordinates without importing the full
canonical-ray / cyclic-gap chain.
-/

namespace JSP000404Research

open Real

/-- Canonical real-linear isometry from our Euclidean plane to the complex
plane. -/
noncomputable def planeToComplex : Plane ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

@[simp] theorem planeToComplex_apply (x : Plane) :
    planeToComplex x = x 0 + x 1 * Complex.I := by
  rfl

@[simp] theorem planeToComplex_rayDirection (theta : ℝ) :
    planeToComplex (rayDirection theta) =
      Real.cos theta + Real.sin theta * Complex.I := by
  simp [planeToComplex, rayDirection]

@[simp] theorem planeToComplex_signedRayDirection
    (sigma : Bool) (theta : ℝ) :
    planeToComplex (signedRayDirection sigma theta) =
      if sigma then
        Real.cos theta + Real.sin theta * Complex.I
      else
        -(Real.cos theta + Real.sin theta * Complex.I) := by
  cases sigma
  · simp only [signedRayDirection, Bool.false_eq_true, ite_false]
    rw [map_neg, planeToComplex_rayDirection]
  · simp only [signedRayDirection, ite_true]
    exact planeToComplex_rayDirection theta

#print axioms planeToComplex_apply
#print axioms planeToComplex_rayDirection
#print axioms planeToComplex_signedRayDirection

end JSP000404Research
