import JSP000404Research.PlanarSevenPointsStrict120Angle
import Mathlib.Tactic

/-!
# Quantitative seven-centre angle slack in the original n=3 lower strip

For every actual seven-or-more-point injective plane configuration, the
already-certified integer-endpoint geometry produces a genuine triangle
with angle strictly above 2*pi/3.  If the same configuration satisfies
AngleCap at lambda = pi/(3+delta), then the original angular excess is
paid by the ACTUAL strip slack:

  3 * t * (angle - (pi - pi/3)) <= pi * delta.

This is a necessary real-geometric condition, independent of any
synthetic Boolean exterior hole or reused dyadic profile credit.
It does NOT provide a uniform margin valid for all point configurations
and does NOT discharge the global JSP-000404 capacity assertion.
-/

namespace JSP000404Research

/-- Pure real-arithmetic conversion from an angle cap at t=3+delta
to an explicit quantitative payment of the excess above 2*pi/3. -/
theorem three_scale_angle_excess_le_strip_slack
    {t delta theta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (ht : t = 3 + delta)
    (hupper : theta ≤ Real.pi - Real.pi / t) :
    3 * t * (theta - (Real.pi - Real.pi / 3)) ≤
      Real.pi * delta := by
  have htpos : 0 < t := by rw [ht]; linarith
  have hdiv : t * (Real.pi / t) = Real.pi := by
    field_simp [ne_of_gt htpos]
  have hmul :
      3 * t * theta ≤ 3 * t * (Real.pi - Real.pi / t) :=
    mul_le_mul_of_nonneg_left hupper (by positivity)
  rw [ht] at hdiv hmul ⊢
  nlinarith [hdiv, hmul]

/-- With >=7 ORIGINAL centres, a genuine distinct-vertex triangle has
strictly positive excess above 120 degrees, and its excess is bounded
by the actual n=3 strip remainder; no configuration-independent
positive margin is asserted. -/
theorem planar_three_seven_actual_angle_excess_le_strip_slack
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 7 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t) :
    ∃ a b c : V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Real.pi - Real.pi / 3 <
        EuclideanGeometry.angle (p a) (p b) (p c) ∧
      3 * t *
        (EuclideanGeometry.angle (p a) (p b) (p c) -
          (Real.pi - Real.pi / 3)) ≤ Real.pi * delta := by
  obtain ⟨a, b, c, hab, hac, hbc, hstrict⟩ :=
    seven_points_have_actual_angle_gt_two_pi_over_three p hp hcard
  have hupper :
      EuclideanGeometry.angle (p a) (p b) (p c) ≤
        Real.pi - Real.pi / t := by
    simpa [hlam] using (hcap a b c hab hac hbc)
  exact ⟨a, b, c, hab, hac, hbc, hstrict,
    three_scale_angle_excess_le_strip_slack hdelta0 ht hupper⟩

/-- For seven or more original centres there is NO actual n=3
AngleCap configuration at a nonpositive strip remainder.
This is an implication of the quantitative witness, not an
assumption used to assert the entire positive-delta region empty. -/
theorem planar_three_seven_angle_cap_forces_strict_positive_delta
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 7 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t) :
    0 < delta := by
  obtain ⟨a, b, c, _, _, _, hstrict, hpaid⟩ :=
    planar_three_seven_actual_angle_excess_le_strip_slack
      hp hcap hcard hdelta0 ht hlam
  have htpos : 0 < t := by rw [ht]; linarith
  have hgap :
      0 < EuclideanGeometry.angle (p a) (p b) (p c) -
        (Real.pi - Real.pi / 3) := sub_pos.mpr hstrict
  have hscaled :
      0 < 3 * t *
        (EuclideanGeometry.angle (p a) (p b) (p c) -
          (Real.pi - Real.pi / 3)) := by
    positivity
  have hdeltaPi : 0 < Real.pi * delta := lt_of_lt_of_le hscaled hpaid
  nlinarith [Real.pi_pos]

#print axioms three_scale_angle_excess_le_strip_slack
#print axioms planar_three_seven_actual_angle_excess_le_strip_slack
#print axioms planar_three_seven_angle_cap_forces_strict_positive_delta

end JSP000404Research
