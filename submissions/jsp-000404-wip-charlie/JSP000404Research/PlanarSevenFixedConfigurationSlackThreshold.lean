import JSP000404Research.PlanarThreeManyAngleSlackCentres
import Mathlib.Tactic

/-!
# Original seven-plus-point configurations have a positive local strip threshold

The seven-point >120-degree theorem and the quantitative planar strip
payment imply a stronger *fixed-configuration* statement:

For each injective finite planar point set with at least seven
original vertices, there is an explicit positive real epsilon(p)
such that NO n=3 AngleCap assignment with 0<=delta<epsilon(p)
can hold for THAT original point map.

This epsilon(p) comes from one actual original witness angle theta:
  epsilon(p) = (9/pi) * (theta - 2*pi/3) > 0.

It is NOT a uniform margin independent of the point positions;
no global cardinality exclusion for all 0<delta<1/2 follows.
No new axioms, admitted proofs, synthetic holes, or nonreuse credits.
-/

namespace JSP000404Research

/-- Strengthen the original real seven-point gap inequality using t>=3:
the angle excess, multiplied by nine, is paid by pi*delta. -/
theorem planar_three_seven_actual_nine_angle_excess_le_pi_delta
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
      9 *
        (EuclideanGeometry.angle (p a) (p b) (p c) -
          (Real.pi - Real.pi / 3)) ≤ Real.pi * delta := by
  obtain ⟨a, b, c, hab, hac, hbc, hwide, hpaid⟩ :=
    planar_three_seven_actual_angle_excess_le_strip_slack
      hp hcap hcard hdelta0 ht hlam
  have htge : (3 : ℝ) ≤ t := by rw [ht]; linarith
  have hgap0 :
      0 ≤ EuclideanGeometry.angle (p a) (p b) (p c) -
        (Real.pi - Real.pi / 3) := (sub_pos.mpr hwide).le
  have hmult :
      0 ≤ (t - 3) *
        (EuclideanGeometry.angle (p a) (p b) (p c) -
          (Real.pi - Real.pi / 3)) :=
    mul_nonneg (sub_nonneg.mpr htge) hgap0
  refine ⟨a, b, c, hab, hac, hbc, hwide, ?_⟩
  nlinarith [hpaid, hmult]

/-- A FIXED actual original point set with >=7 centres has its own
strictly positive n=3 admissible strip lower bound. The chosen
bound is computed from a specific >120-degree witness of that set.
It is not uniform across varying original configurations. -/
theorem seven_original_points_have_positive_configuration_strip_threshold
    {V : Type*} [LinearOrder V] [Fintype V]
    (p : V → Plane)
    (hp : Function.Injective p)
    (hcard : 7 ≤ Fintype.card V) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧
      ∀ (lam t delta : ℝ),
        0 ≤ delta →
        t = (3 : ℝ) + delta →
        lam = Real.pi / t →
        AngleCap p lam →
        epsilon ≤ delta := by
  obtain ⟨a, b, c, hab, hac, hbc, hwide⟩ :=
    seven_points_have_actual_angle_gt_two_pi_over_three p hp hcard
  let gap :=
    EuclideanGeometry.angle (p a) (p b) (p c) -
      (Real.pi - Real.pi / 3)
  let epsilon : ℝ := 9 * gap / Real.pi
  have hgap : 0 < gap := sub_pos.mpr hwide
  have heps : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos (by positivity) Real.pi_pos
  refine ⟨epsilon, heps, ?_⟩
  intro lam t delta hdelta0 ht hlam hcap
  have hupper :
      EuclideanGeometry.angle (p a) (p b) (p c) ≤
        Real.pi - Real.pi / t := by
    simpa [hlam] using (hcap a b c hab hac hbc)
  have hpaid :=
    three_scale_angle_excess_le_strip_slack hdelta0 ht hupper
  have htge : (3 : ℝ) ≤ t := by rw [ht]; linarith
  have hmult : 0 ≤ (t - 3) * gap :=
    mul_nonneg (sub_nonneg.mpr htge) hgap.le
  have hnine : 9 * gap ≤ Real.pi * delta := by
    dsimp [gap] at hmult ⊢
    nlinarith [hpaid, hmult]
  dsimp [epsilon]
  exact (div_le_iff₀ Real.pi_pos).2 (by nlinarith [hnine])

#print axioms planar_three_seven_actual_nine_angle_excess_le_pi_delta
#print axioms seven_original_points_have_positive_configuration_strip_threshold

end JSP000404Research
