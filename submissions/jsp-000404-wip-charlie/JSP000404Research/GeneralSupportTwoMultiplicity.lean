import JSP000404Research.SharpCentre
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Global contradiction from two sharp-relative small outer centres

Fix a distinguished sharp centre s.  The arbitrary-cardinality support-two
geometry is aiming at the following local property for a deficit-two centre i:

  every pair of rays from i avoiding s makes angle at most delta*lambda.

This file packages that property independently of how it is proved.

If two distinct centres a,b both have this property, choose any fourth point c
distinct from s,a,b.  Then in triangle a-b-c the angles at a and b are each at
most delta*lambda, while the global Sendov cap bounds the angle at c by
pi-lambda.  For delta<1/2 these three upper bounds sum to strictly less than
pi, contradicting the Euclidean triangle angle sum.

Thus any eventual proof that every support-two deficit-two centre around s has
this local property immediately yields multiplicity at most one.
-/

namespace JSP000404Research

open Real

def OuterSmallAwayFrom
    {V : Type*}
    (p : V → Plane) (delta lam : ℝ)
    (s i : V) : Prop :=
  ∀ j k,
    j ≠ i → k ≠ i →
    j ≠ s → k ≠ s →
    j ≠ k →
    EuclideanGeometry.angle (p j) (p i) (p k) ≤
      delta * lam

theorem two_outerSmallAwayFrom_no_fourth
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : OuterSmallAwayFrom p delta lam s a)
    (hb : OuterSmallAwayFrom p delta lam s b) :
    False := by
  have hA :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤
        delta * lam :=
    ha b c hab.symm hac
      hsb.symm hsc.symm hbc
  have hB :
      EuclideanGeometry.angle (p a) (p b) (p c) ≤
        delta * lam :=
    hb a c hab hbc
      hsa.symm hsc.symm hac
  have hC :
      EuclideanGeometry.angle (p a) (p c) (p b) ≤
        Real.pi - lam :=
    hcap a c b hac hab hbc.symm
  have hsum :
      EuclideanGeometry.angle (p b) (p a) (p c) +
        EuclideanGeometry.angle (p a) (p c) (p b) +
        EuclideanGeometry.angle (p c) (p b) (p a) =
          Real.pi := by
    simpa [add_assoc, add_left_comm, add_comm,
      EuclideanGeometry.angle_comm (p c) (p b) (p a)] using
      (EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p b) (p₂ := p a) (p c)
        (hp.ne hab.symm))
  have hBcomm :
      EuclideanGeometry.angle (p c) (p b) (p a) =
        EuclideanGeometry.angle (p a) (p b) (p c) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hBcomm] at hsum
  have htwo : 2 * delta * lam < lam := by
    nlinarith
  nlinarith

/-- Three explicit non-sharp vertices cannot contain two distinct centres
having the sharp-relative small-angle property. -/
theorem no_two_outerSmallAwayFrom_among_three
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : OuterSmallAwayFrom p delta lam s a)
    (hb : OuterSmallAwayFrom p delta lam s b) :
    False :=
  two_outerSmallAwayFrom_no_fourth
    hp hcap hdelta hlampos
    hsa hsb hsc hab hac hbc ha hb

#print axioms two_outerSmallAwayFrom_no_fourth
#print axioms no_two_outerSmallAwayFrom_among_three

end JSP000404Research
