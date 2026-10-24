import JSP000404Research.SharpCentre
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Tactic

/-!
# Original-plane AngleCap excludes collinear triples

If lambda is positive, a collinear triple of distinct source points
would produce a straight angle pi at one of those points, contradicting
the uniform upper cap pi - lambda. This is the *actual planar geometry*,
not a projective or Boolean-word surrogate.
-/

namespace JSP000404Research

/-- Three distinct original centres cannot be collinear under a positive
global angle cap. -/
theorem angleCap_not_collinear_of_distinct
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam : ℝ} (hcap : AngleCap p lam) (hlam : 0 < lam)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Collinear ℝ ({p a, p b, p c} : Set Plane) := by
  intro hcol
  have hsplit :=
    (EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi).1 hcol
  rcases hsplit with heqab | heqcb | hzero | hpi
  · exact hab (hp heqab)
  · exact hbc ((hp heqcb).symm)
  · rcases (EuclideanGeometry.angle_eq_zero_iff_eq_and_ne_or_sbtw).1 hzero with
        ⟨heqac, _⟩ | hs1 | hs2
    · exact hac (hp heqac)
    · have hstraight :
          EuclideanGeometry.angle (p b) (p a) (p c) = Real.pi :=
        (EuclideanGeometry.angle_eq_pi_iff_sbtw).2 hs1
      have hbound := hcap b a c hab.symm hbc hac
      linarith
    · have hstraight :
          EuclideanGeometry.angle (p b) (p c) (p a) = Real.pi :=
        (EuclideanGeometry.angle_eq_pi_iff_sbtw).2 hs2
      have hbound := hcap b c a hbc hab.symm hac.symm
      linarith
  · have hbound := hcap a b c hab hac hbc
    linarith

/-- Every genuine three-centre angle is strictly positive when the
original-plane global AngleCap has positive lambda. -/
theorem angleCap_actual_angle_pos_of_distinct
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam : ℝ} (hcap : AngleCap p lam) (hlam : 0 < lam)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    0 < EuclideanGeometry.angle (p a) (p b) (p c) := by
  exact EuclideanGeometry.angle_pos_of_not_collinear
    (angleCap_not_collinear_of_distinct hp hcap hlam hab hac hbc)

#print axioms angleCap_not_collinear_of_distinct
#print axioms angleCap_actual_angle_pos_of_distinct

end JSP000404Research
