import JSP000404Research.StrictExposure
import Mathlib.Tactic

/-!
# Strict exposure from a positive transition cut

Suppose the projective direction circle at a centre has circumference pi.
Cut it across a nonempty gap of angular width g>0.  The complementary lifted
interval then has width pi-g<pi.

If every ray from the centre admits a positive-scalar representation with one
common Boolean sign and a direction parameter in that complementary interval,
the centre is strictly exposed by the midpoint-direction argument already
proved in StrictExposure.

This is the geometric half of the intended

  support <= 2 -> exactly one sign transition -> hull/exposed centre

bridge.  The remaining step is finite cyclic bookkeeping: the unique sign
transition must be used as the cut, and positivity of its quotient supplies
g >= lambda > 0.
-/

namespace JSP000404Research

open Real

/-- A positive removed projective gap leaves a strict sub-pi complement. -/
theorem pi_sub_gap_lt_pi
    {gap : ℝ} (hgap : 0 < gap) :
    Real.pi - gap < Real.pi := by
  linarith

/-- Quantitative cap-unit version. -/
theorem pi_sub_gap_le_pi_sub_lam
    {gap lam : ℝ}
    (hgap : lam ≤ gap) :
    Real.pi - gap ≤ Real.pi - lam := by
  linarith

/-- Cutting the projective circle at a positive gap and obtaining a common
sign on the complementary lift gives a strict supporting line. -/
theorem strictlyExposedAt_of_positive_transition_cut
    {V : Type*} {p : V → Plane}
    {i : V} {a gap : ℝ}
    (hgap0 : 0 < gap)
    (hgappi : gap ≤ Real.pi)
    (sigma : Bool)
    (hrepr : ∀ j, j ≠ i →
      ∃ rho : ℝ, ∃ theta : ℝ,
        0 < rho ∧
        a ≤ theta ∧ theta ≤ a + (Real.pi - gap) ∧
        p j - p i = rho • signedRayDirection sigma theta) :
    StrictlyExposedAt p i := by
  apply strictlyExposedAt_of_common_signed_interval
    (a := a) (width := Real.pi - gap)
  · linarith
  · exact pi_sub_gap_lt_pi hgap0
  · exact sigma
  · exact hrepr

/-- In Sendov scaling it suffices that the removed transition gap contain one
full cap unit lambda. -/
theorem strictlyExposedAt_of_transition_gap_ge_lam
    {V : Type*} {p : V → Plane}
    {i : V} {a gap lam : ℝ}
    (hlam : 0 < lam)
    (hgap : lam ≤ gap)
    (hgappi : gap ≤ Real.pi)
    (sigma : Bool)
    (hrepr : ∀ j, j ≠ i →
      ∃ rho : ℝ, ∃ theta : ℝ,
        0 < rho ∧
        a ≤ theta ∧ theta ≤ a + (Real.pi - gap) ∧
        p j - p i = rho • signedRayDirection sigma theta) :
    StrictlyExposedAt p i := by
  exact strictlyExposedAt_of_positive_transition_cut
    (p := p) (i := i) (a := a) (gap := gap)
    (lt_of_lt_of_le hlam hgap) hgappi sigma hrepr

#print axioms pi_sub_gap_lt_pi
#print axioms strictlyExposedAt_of_positive_transition_cut
#print axioms strictlyExposedAt_of_transition_gap_ge_lam

end JSP000404Research
