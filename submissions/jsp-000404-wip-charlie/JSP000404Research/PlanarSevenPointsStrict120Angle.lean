import JSP000404Research.PlanarThreeIntegerCardinalityCap
import Mathlib.Tactic

/-!
# Actual seven-point strict angle threshold at the integer n=3 endpoint

The kernel-certified true original-plane result says: any injective
finite planar point set satisfying the uniform angle cap
  angle(a,b,c) <= pi - pi/3
has cardinality at most SIX, using genuine projective gap and
strict-transition arc packing geometry.

Consequently, for ANY ACTUAL distinct planar configuration with
SEVEN or more original points, there must be a genuine original
ordered triangle with angle STRICTLY GREATER than 2*pi/3.

Unlike merely obtaining an abstract dyadic capacity estimate,
this states a direct Euclidean angle fact about the ORIGINAL point
map. The centre cycles needed by the packing proof are constructed
from the injective original coordinates, not assumed as extra
hypotheses. No geometric Hall certificate, Boolean hole or admitted
axiom is invoked.

This is a strict integer-endpoint statement; it does not supply a
uniform positive margin beyond 2*pi/3 across all configurations.
-/

namespace JSP000404Research

/-- ORIGINAL plane geometry: every seven-or-more distinct points
contain an honest triangle with actual angle >120 degrees.
All projective cycles are constructed from the input points. -/
theorem seven_points_have_actual_angle_gt_two_pi_over_three
    {V : Type*} [LinearOrder V] [Fintype V]
    (p : V → Plane)
    (hp : Function.Injective p)
    (hcard : 7 ≤ Fintype.card V) :
    ∃ a b c : V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Real.pi - Real.pi / 3 <
        EuclideanGeometry.angle (p a) (p b) (p c) := by
  classical
  have hother (i : V) : Nonempty (OtherVertex i) := by
    apply Fintype.card_pos_iff.mp
    change 0 < Fintype.card {j : V // j ≠ i}
    rw [Fintype.card_subtype_compl (fun j : V => j = i),
      Fintype.card_subtype_eq]
    omega
  let cycles : ∀ i : V, CentreProjectiveCycle hp i :=
    fun i => Classical.choice (exists_centreProjectiveCycle hp i (hother i))
  by_contra hno
  have hcap : AngleCap p (Real.pi / 3) := by
    intro a b c hab hac hbc
    by_contra hnot
    apply hno
    exact ⟨a,b,c,hab,hac,hbc,lt_of_not_ge hnot⟩
  have hbound : Fintype.card V ≤ 6 :=
    planar_three_integer_card_le_six hp hcap
      (by rfl : (3 : ℝ) = 3)
      (by rfl : Real.pi / 3 = Real.pi / (3 : ℝ))
      cycles
  omega

#print axioms seven_points_have_actual_angle_gt_two_pi_over_three

end JSP000404Research
