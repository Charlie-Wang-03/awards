import JSP000404Research.PlanarSevenFixedConfigurationSlackThreshold
import Mathlib.Tactic

/-!
# Exact angular strip threshold for a fixed seven-plus-point configuration

The previous original seven-point stability certificate used the first-order
linear estimate delta >= 9*(theta - 2*pi/3)/pi.  The ACTUAL AngleCap
condition gives a sharper exact real inequality:

    delta >= pi/(pi-theta) - 3,

where theta is any genuine original angle bounded by pi-pi/(3+delta).

The denominator must be strictly positive; this follows from the
positive-angle gap in the ACTUAL cap.  For a fixed planar configuration
with >=7 points, choose a certified >120-degree original angle theta.
If theta < pi, the strict positive threshold above applies. If theta
is pi (collinear), no finite positive-t AngleCap is possible and any
positive local threshold is valid.

Thus every fixed original seven-plus configuration admits an exact
angle-derived positive admissibility gap, with no artificial uniform
lower bound over all configurations and no global eight-source credit.
-/

namespace JSP000404Research

/-- Exact scale conversion; no local/global geometry premise is used. -/
theorem three_scale_exact_angle_threshold
    {t delta theta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (ht : t = (3 : ℝ) + delta)
    (hupper : theta ≤ Real.pi - Real.pi / t) :
    Real.pi / (Real.pi - theta) - 3 ≤ delta := by
  have htpos : 0 < t := by rw [ht]; linarith
  have hpi : 0 < Real.pi / t := div_pos Real.pi_pos htpos
  have hden : 0 < Real.pi - theta := by linarith
  have hq : Real.pi / t ≤ Real.pi - theta := by linarith
  have hmul : Real.pi ≤ (Real.pi - theta) * t :=
    (div_le_iff₀ htpos).mp hq
  have hbound : Real.pi / (Real.pi - theta) ≤ t :=
    (div_le_iff₀ hden).mpr (by nlinarith [hmul])
  rw [ht] at hbound
  linarith

/-- A strict >120-degree actual angle, as long as it is <180 degrees,
has a strictly positive EXACT normalized strip threshold. -/
theorem three_scale_exact_angle_threshold_pos
    {theta : ℝ}
    (hwide : Real.pi - Real.pi / 3 < theta)
    (hltpi : theta < Real.pi) :
    0 < Real.pi / (Real.pi - theta) - 3 := by
  have hden : 0 < Real.pi - theta := sub_pos.mpr hltpi
  have hangle : 3 * (Real.pi - theta) < Real.pi := by
    nlinarith [hwide]
  have hgt : (3 : ℝ) < Real.pi / (Real.pi - theta) :=
    (lt_div_iff₀ hden).2 (by nlinarith [hangle])
  linarith

/-- Every FIXED injective planar set of >=7 ORIGINAL vertices has a
positive lower n=3 strip threshold. If its chosen strict >120-degree
witness is <180 degrees, use the exact reciprocal formula; if it is
180 degrees, no positive-t AngleCap exists for that fixed point map.

The theorem is unconditional in the original plane map, but its
positive epsilon is CONFIGURATION-DEPENDENT. -/
theorem seven_original_points_have_exact_configuration_strip_threshold
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
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hwide⟩ :=
    seven_points_have_actual_angle_gt_two_pi_over_three p hp hcard
  let theta := EuclideanGeometry.angle (p a) (p b) (p c)
  by_cases hltpi : theta < Real.pi
  · let epsilon : ℝ := Real.pi / (Real.pi - theta) - 3
    have heps : 0 < epsilon :=
      three_scale_exact_angle_threshold_pos hwide hltpi
    refine ⟨epsilon, heps, ?_⟩
    intro lam t delta hdelta0 ht hlam hcap
    have hupper : theta ≤ Real.pi - Real.pi / t := by
      simpa [theta, hlam] using (hcap a b c hab hac hbc)
    exact three_scale_exact_angle_threshold hdelta0 ht hupper
  · refine ⟨(1 : ℝ), by norm_num, ?_⟩
    intro lam t delta hdelta0 ht hlam hcap
    have htpos : 0 < t := by rw [ht]; linarith
    have hpos : 0 < Real.pi / t :=
      div_pos Real.pi_pos htpos
    have hupper : theta ≤ Real.pi - Real.pi / t := by
      simpa [theta, hlam] using (hcap a b c hab hac hbc)
    have htheta : Real.pi ≤ theta := le_of_not_gt hltpi
    exfalso
    linarith

#print axioms three_scale_exact_angle_threshold
#print axioms three_scale_exact_angle_threshold_pos
#print axioms seven_original_points_have_exact_configuration_strip_threshold

end JSP000404Research
