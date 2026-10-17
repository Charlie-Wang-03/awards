import JSP000404Research.SharpCentre
import Mathlib.Tactic

/-!
# Genuine n=1 lower-branch obstruction: AngleCap forbids three centres

For t = 1+delta and 0 <= delta < 1/2, the angle-cap parameter
lambda = pi/t is STRICTLY greater than 2*pi/3. Three different
actual planar points would form a triangle in which all three
interior angles are <= pi-lambda < pi/3, contradicting the exact
triangle angle-sum pi. Thus the entire n=1 branch necessarily has
at most two original centres. No quotient cycles, Boolean hole
credits, or unreserved surpluses are assumed in this obstruction.
-/

namespace JSP000404Research

theorem lower_one_angleCap_forbids_three
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (1 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    False := by
  have htpos : 0 < t := by rw [ht]; linarith
  have htShort : 2 * t < 3 := by rw [ht]; linarith
  have hmul :
      (2 * t) * Real.pi < 3 * Real.pi :=
    mul_lt_mul_of_pos_right htShort Real.pi_pos
  have hlarge :
      (2 : ℝ) * Real.pi / 3 < lam := by
    rw [hlam]
    apply (lt_div_iff₀ htpos).2
    nlinarith
  have ha :
      EuclideanGeometry.angle (p b) (p a) (p c)
        ≤ Real.pi - lam :=
    hcap b a c hab.symm hbc hac
  have hb :
      EuclideanGeometry.angle (p a) (p b) (p c)
        ≤ Real.pi - lam :=
    hcap a b c hab hac hbc
  have hc :
      EuclideanGeometry.angle (p a) (p c) (p b)
        ≤ Real.pi - lam :=
    hcap a c b hac hab hbc.symm
  have hsum :
      EuclideanGeometry.angle (p b) (p a) (p c) +
      EuclideanGeometry.angle (p a) (p b) (p c) +
      EuclideanGeometry.angle (p a) (p c) (p b) = Real.pi := by
    have htri :=
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p b) (p₂ := p a) (p c) (hp.ne hab)
    simpa [EuclideanGeometry.angle_comm,
      add_assoc, add_left_comm, add_comm] using htri
  linarith

theorem original_card_le_two_of_lower_one
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (1 : ℝ) + delta)
    (hlam : lam = Real.pi / t) :
    Fintype.card V ≤ 2 := by
  classical
  by_contra hnot
  have hcard :
      2 < (Finset.univ : Finset V).card := by
    simpa using (show 2 < Fintype.card V by omega)
  obtain ⟨a, b, c, _, _, _, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp hcard
  exact lower_one_angleCap_forbids_three
    hp hcap hdelta0 hdeltaHalf ht hlam hab hac hbc

#print axioms lower_one_angleCap_forbids_three
#print axioms original_card_le_two_of_lower_one

end JSP000404Research
