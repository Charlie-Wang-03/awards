
import JSP000404Research.ScaledCyclicBandBudget
import JSP000404Research.CentreQuotientData
import Mathlib.Tactic

/-!
# Scaling canonical projective angles to the Sendov t-circle

For a canonical projective angle theta in [0,pi), put

  x(theta) = t*theta/pi.

Then the cyclic projective gaps, after multiplying by t, become exactly the
ordinary cyclic gaps of the scaled x-coordinates on a circle of circumference
t.

Consequently the concrete Sendov quotient list

  floor(t * normalizedProjectiveGap)

is exactly the list of natural floors of the scaled cyclic real gaps.

This is the exact representation bridge needed to apply ScaledCyclicBandBudget
to CentreProjectiveCycle.
-/

namespace JSP000404Research

open Real

def scaleProjectiveAngle (t theta : ℝ) : ℝ :=
  t * theta / Real.pi

def scaleProjectiveGap (t g : ℝ) : ℝ :=
  t * (g / Real.pi)

theorem getLastD_map_scaleProjectiveAngle
    (t a : ℝ) (xs : List ℝ) :
    (xs.map (scaleProjectiveAngle t)).getLastD
        (scaleProjectiveAngle t a)
      =
    scaleProjectiveAngle t (xs.getLastD a) := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons b bs ih =>
      simpa [List.getLastD_cons] using ih b

theorem successiveDiffsFrom_scaleProjectiveAngle
    (t a : ℝ) (xs : List ℝ) :
    successiveDiffsFrom
        (scaleProjectiveAngle t a)
        (xs.map (scaleProjectiveAngle t))
      =
    (successiveDiffsFrom a xs).map
      (scaleProjectiveGap t) := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons b bs ih =>
      simp only [successiveDiffsFrom, List.map_cons]
      congr 1
      · unfold scaleProjectiveAngle scaleProjectiveGap
        ring
      · exact ih b

/-- Exact scaled cyclic-gap identity. -/
theorem cyclicGapsAt_scaleProjectiveAngle
    (t a : ℝ) (xs : List ℝ) :
    cyclicGapsAt t
        ((a :: xs).map (scaleProjectiveAngle t))
      =
    (projectiveGaps (a :: xs)).map
      (scaleProjectiveGap t) := by
  simp only [List.map_cons, cyclicGapsAt, projectiveGaps]
  rw [successiveDiffsFrom_scaleProjectiveAngle]
  rw [getLastD_map_scaleProjectiveAngle]
  congr 1
  unfold scaleProjectiveAngle scaleProjectiveGap
  field_simp [Real.pi_ne_zero]
  ring

/-- Natural floors of the scaled cyclic gaps are exactly the concrete
quotient list. -/
theorem floor_scaled_cyclicGaps_eq_quotientList
    (t a : ℝ) (xs : List ℝ) :
    (cyclicGapsAt t
        ((a :: xs).map (scaleProjectiveAngle t))).map
          Nat.floor
      =
    quotientList t
      (normalizedProjectiveGaps (a :: xs)) := by
  rw [cyclicGapsAt_scaleProjectiveAngle]
  simp [quotientList, normalizedProjectiveGaps,
    scaleProjectiveGap, List.map_map]

/-- Scaled canonical angle is the normalized ray coordinate used by the direct
projective-band partition. -/
theorem scaleProjectiveAngle_rayTheta_eq_normalizedRayTheta
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t : ℝ) (i : V) (j : OtherVertex i) :
    scaleProjectiveAngle t (rayThetaAt hp i j) =
      normalizedRayTheta hp t i j := by
  rfl

#print axioms getLastD_map_scaleProjectiveAngle
#print axioms successiveDiffsFrom_scaleProjectiveAngle
#print axioms cyclicGapsAt_scaleProjectiveAngle
#print axioms floor_scaled_cyclicGaps_eq_quotientList

end JSP000404Research
