import Mathlib.Tactic

/-!
# Width of a wrap-triangle phase obstruction

Write the normalized projective circumference as

  t = n + delta.

A triangle whose three edge directions fit into the merged wrap colour occupies
an arc of length at most 1+delta.  If g is the complementary (largest)
projective direction gap, the available phase slack is

  (1+delta) - (t-g) = g - (n-1).

The global angle cap gives g <= n+delta-1.  Therefore whenever the wrap
obstruction is nonempty, i.e. g >= n-1, its phase width lies in [0,delta].

This is only the real-arithmetic width calculation.  The geometric statement
identifying wrap triangles with such direction triples remains separate.
-/

namespace JSP000404Research

/-- Algebraic identity for the phase slack of a wrap triangle. -/
theorem wrap_slack_identity
    {n : ℕ} {delta g : ℝ} :
    (1 + delta) - (((n : ℝ) + delta) - g) =
      g - ((n : ℝ) - 1) := by
  ring

/-- Under the global cap, every nonempty wrap-triangle obstruction has width
at most delta. -/
theorem wrap_obstruction_width_bounds
    {n : ℕ} {delta g : ℝ}
    (hlarge : (n : ℝ) - 1 ≤ g)
    (hcap : g ≤ (n : ℝ) + delta - 1) :
    0 ≤ g - ((n : ℝ) - 1) ∧
      g - ((n : ℝ) - 1) ≤ delta := by
  constructor <;> linarith

/-- Equivalent formulation using the occupied direction span
span = t-g. -/
theorem wrap_phase_slack_le_delta
    {n : ℕ} {delta g span : ℝ}
    (hspan : span = ((n : ℝ) + delta) - g)
    (hfit : span ≤ 1 + delta)
    (hcap : g ≤ (n : ℝ) + delta - 1) :
    0 ≤ (1 + delta) - span ∧
      (1 + delta) - span ≤ delta := by
  subst span
  have hlarge : (n : ℝ) - 1 ≤ g := by
    linarith
  rw [wrap_slack_identity]
  exact wrap_obstruction_width_bounds hlarge hcap

#print axioms wrap_slack_identity
#print axioms wrap_obstruction_width_bounds
#print axioms wrap_phase_slack_le_delta

end JSP000404Research
