import JSP000404Research.ProjectiveInterval
import Mathlib.Tactic

/-!
# Sign monodromy on the projective direction circle

The projective direction parameter has period pi, but an oriented ray does not:
advancing the representative by pi negates the unit direction.

Therefore a signed representation satisfies

  signedRayDirection (!sigma) (theta + pi)
    = signedRayDirection sigma theta.

So after one full circuit of the projective direction circle the Boolean sign
must flip.  Any cyclic sign-transition count must use this antiperiodic
boundary condition rather than ordinary periodicity.
-/

namespace JSP000404Research

open Real

/-- Advancing an ordinary direction parameter by pi negates the unit vector. -/
theorem rayDirection_add_pi (theta : ℝ) :
    rayDirection (theta + Real.pi) = - rayDirection theta := by
  ext i
  fin_cases i <;>
    simp [rayDirection, Real.cos_add_pi, Real.sin_add_pi]

/-- Equivalent subtraction form. -/
theorem rayDirection_sub_pi (theta : ℝ) :
    rayDirection (theta - Real.pi) = - rayDirection theta := by
  have h := rayDirection_add_pi (theta - Real.pi)
  convert h using 1 <;> ring

/-- The signed representation is antiperiodic in its Boolean sign. -/
theorem signedRayDirection_not_add_pi
    (sigma : Bool) (theta : ℝ) :
    signedRayDirection (!sigma) (theta + Real.pi) =
      signedRayDirection sigma theta := by
  cases sigma <;>
    simp [signedRayDirection, rayDirection_add_pi]

/-- Moving the parameter backwards by pi has the same sign-flip rule. -/
theorem signedRayDirection_not_sub_pi
    (sigma : Bool) (theta : ℝ) :
    signedRayDirection (!sigma) (theta - Real.pi) =
      signedRayDirection sigma theta := by
  cases sigma <;>
    simp [signedRayDirection, rayDirection_sub_pi]

#print axioms rayDirection_add_pi
#print axioms rayDirection_sub_pi
#print axioms signedRayDirection_not_add_pi
#print axioms signedRayDirection_not_sub_pi

end JSP000404Research
