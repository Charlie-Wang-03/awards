import JSP000404Research.CrossingDiagonalsQuadrilateralAngleSum
import JSP000404Research.SharpCentre
import Mathlib.Tactic

/-!
# Convex four-cycles cannot contain two strict sub-lambda vertex angles

For true crossing diagonals, the four actual vertex angles total 2*pi.
Two strict small angles and the global caps at the other vertices then
contradict this equality. No hypothesis identifies an abstract colour
C4 with a crossing-diagonal convex quadrilateral.
-/

namespace JSP000404Research

/-- A genuinely convex four-cycle under actual AngleCap cannot have
two opposite vertex angles strictly below lambda. -/
theorem convex_four_cycle_no_two_opposite_angles_lt_lam
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam : ℝ} (hcap : AngleCap p lam)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : p a ∉ convexHull ℝ ({p b, p c, p d} : Set Plane))
    (hc : p c ∉ convexHull ℝ ({p a, p b, p d} : Set Plane))
    (hcross : (segment ℝ (p a) (p c) ∩
      segment ℝ (p b) (p d)).Nonempty)
    (hsmallA :
      EuclideanGeometry.angle (p b) (p a) (p d) < lam)
    (hsmallC :
      EuclideanGeometry.angle (p b) (p c) (p d) < lam) :
    False := by
  have hB : EuclideanGeometry.angle (p a) (p b) (p c) ≤
      Real.pi - lam := hcap a b c hab hac hbc
  have hD : EuclideanGeometry.angle (p c) (p d) (p a) ≤
      Real.pi - lam := hcap c d a hcd hac.symm had.symm
  have hsum :=
    crossing_diagonals_four_angles_sum_two_pi
      (a := p a) (b := p b) (c := p c) (d := p d)
      (fun eq => hab (hp eq))
      (fun eq => hac (hp eq))
      (fun eq => had (hp eq))
      (fun eq => hbc (hp eq))
      (fun eq => hbd (hp eq))
      (fun eq => hcd (hp eq))
      ha hc hcross
  linarith only [hB, hD, hsmallA, hsmallC, hsum]

/-- The same geometric obstruction also rules out TWO ADJACENT
strictly sub-lambda angles on the boundary of an actual convex C4. -/
theorem convex_four_cycle_no_two_adjacent_angles_lt_lam
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam : ℝ} (hcap : AngleCap p lam)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : p a ∉ convexHull ℝ ({p b, p c, p d} : Set Plane))
    (hc : p c ∉ convexHull ℝ ({p a, p b, p d} : Set Plane))
    (hcross : (segment ℝ (p a) (p c) ∩
      segment ℝ (p b) (p d)).Nonempty)
    (hsmallA :
      EuclideanGeometry.angle (p b) (p a) (p d) < lam)
    (hsmallB :
      EuclideanGeometry.angle (p a) (p b) (p c) < lam) :
    False := by
  have hC : EuclideanGeometry.angle (p b) (p c) (p d) ≤
      Real.pi - lam := hcap b c d hbc hbd hcd
  have hD : EuclideanGeometry.angle (p c) (p d) (p a) ≤
      Real.pi - lam := hcap c d a hcd hac.symm had.symm
  have hsum :=
    crossing_diagonals_four_angles_sum_two_pi
      (a := p a) (b := p b) (c := p c) (d := p d)
      (fun eq => hab (hp eq))
      (fun eq => hac (hp eq))
      (fun eq => had (hp eq))
      (fun eq => hbc (hp eq))
      (fun eq => hbd (hp eq))
      (fun eq => hcd (hp eq))
      ha hc hcross
  linarith only [hC, hD, hsmallA, hsmallB, hsum]

#print axioms convex_four_cycle_no_two_adjacent_angles_lt_lam

#print axioms convex_four_cycle_no_two_opposite_angles_lt_lam

end JSP000404Research
