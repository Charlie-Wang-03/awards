import JSP000404Research.ProjectiveInterval
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

/-!
# Canonical projective representation of a nonzero planar ray

Every nonzero vector in the Euclidean plane admits a positive-radius signed
projective representation

  x = rho • signedRayDirection sigma theta

with

  rho > 0,   0 <= theta < pi.

We obtain it from the ordinary complex argument in (-pi,pi].  Negative
arguments are shifted by pi and represented with the negative sign; the
endpoint arg=pi is represented by theta=0 with negative sign.  Thus theta
always belongs to the half-open projective interval [0,pi).

This is the first genuine geometric input for the cyclic-gap bridge.
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
  cases sigma <;>
    simp [signedRayDirection, planeToComplex_rayDirection]

/-- The plane-to-complex isometry preserves nonzeroness. -/
theorem planeToComplex_ne_zero
    {x : Plane} (hx : x ≠ 0) :
    planeToComplex x ≠ 0 := by
  exact map_ne_zero_of_injective planeToComplex.injective hx

/-- Polar recovery in plane coordinates at the ordinary complex argument. -/
theorem norm_smul_rayDirection_arg
    {x : Plane} (hx : x ≠ 0) :
    x =
      ‖planeToComplex x‖ •
        rayDirection (Complex.arg (planeToComplex x)) := by
  apply planeToComplex.injective
  simp only [map_smul, planeToComplex_rayDirection]
  have hpolar :=
    Complex.norm_mul_cos_add_sin_mul_I (planeToComplex x)
  simpa [smul_eq_mul] using hpolar.symm

/-- Main canonical projective-ray representation. -/
theorem exists_canonical_projective_representation
    {x : Plane} (hx : x ≠ 0) :
    ∃ rho : ℝ, ∃ sigma : Bool, ∃ theta : ℝ,
      0 < rho ∧
      0 ≤ theta ∧ theta < Real.pi ∧
      x = rho • signedRayDirection sigma theta := by
  let z : ℂ := planeToComplex x
  have hz : z ≠ 0 := by
    dsimp [z]
    exact planeToComplex_ne_zero hx
  have hrho : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpolar :
      x = ‖z‖ • rayDirection (Complex.arg z) := by
    simpa [z] using norm_smul_rayDirection_arg hx
  by_cases hneg : Complex.arg z < 0
  · refine ⟨‖z‖, false, Complex.arg z + Real.pi,
      hrho, ?_, ?_, ?_⟩
    · have harglow := Complex.neg_pi_lt_arg z
      linarith
    · linarith [Real.pi_pos]
    · rw [signedRayDirection]
      simp only [Bool.false_eq_true, if_false]
      have hshift :=
        rayDirection_add_pi (Complex.arg z)
      rw [hshift]
      simpa using hpolar
  · have harg0 : 0 ≤ Complex.arg z := le_of_not_gt hneg
    by_cases hpi : Complex.arg z = Real.pi
    · refine ⟨‖z‖, false, 0, hrho,
        le_rfl, Real.pi_pos, ?_⟩
      rw [signedRayDirection]
      simp only [Bool.false_eq_true, if_false]
      rw [hpi] at hpolar
      have hpiRay := rayDirection_add_pi 0
      norm_num at hpiRay
      rw [hpiRay] at hpolar
      simpa using hpolar
    · refine ⟨‖z‖, true, Complex.arg z,
        hrho, harg0, ?_, ?_⟩
      · exact (Complex.arg_le_pi z).lt_of_ne hpi
      · simpa [signedRayDirection] using hpolar

/-- Convenience form for a displacement between two distinct planar points. -/
theorem exists_canonical_projective_representation_sub
    {a b : Plane} (hab : a ≠ b) :
    ∃ rho : ℝ, ∃ sigma : Bool, ∃ theta : ℝ,
      0 < rho ∧
      0 ≤ theta ∧ theta < Real.pi ∧
      b - a = rho • signedRayDirection sigma theta := by
  apply exists_canonical_projective_representation
  intro hzero
  apply hab
  exact sub_eq_zero.mp hzero.symm

#print axioms planeToComplex_rayDirection
#print axioms norm_smul_rayDirection_arg
#print axioms exists_canonical_projective_representation
#print axioms exists_canonical_projective_representation_sub

end JSP000404Research
