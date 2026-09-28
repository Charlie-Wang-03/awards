import JSP000404Research.HamiltonianResidualSeparation
import Mathlib.Tactic

/-!
# Four-angle budget interface for the Hamiltonian residual

The current hard terminal is described by four small angles

  A = angle(c,b,x)
  B = angle(y,b,z)
  C = angle(b,c,y)
  D = angle(x,c,z)

with A+B <= delta*lambda and C+D <= delta*lambda.

In the lower Sendov branch delta < 1/2, these inequalities force

  A+B+C+D < lambda.

Therefore the terminal is eliminated by the single five-point geometric
statement

  lambda <= A+B+C+D.

This file formalizes that reduction without assuming the still-unproved
five-point budget itself.
-/

namespace JSP000404Research

open Real

def HamiltonianFourAngleBudget
    {V : Type*} (p : V → Plane) (lam : ℝ)
    (b c x y z : V) : Prop :=
  lam ≤
    EuclideanGeometry.angle (p c) (p b) (p x) +
    EuclideanGeometry.angle (p y) (p b) (p z) +
    EuclideanGeometry.angle (p b) (p c) (p y) +
    EuclideanGeometry.angle (p x) (p c) (p z)

/-- The two residual matching inequalities put the four-angle sum strictly
below lambda throughout the lower branch. -/
theorem hamiltonian_residual_four_angle_sum_lt
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    {b c x y z : V}
    (hB :
      EuclideanGeometry.angle (p c) (p b) (p x) +
          EuclideanGeometry.angle (p y) (p b) (p z)
        ≤ delta * lam)
    (hC :
      EuclideanGeometry.angle (p b) (p c) (p y) +
          EuclideanGeometry.angle (p x) (p c) (p z)
        ≤ delta * lam) :
    EuclideanGeometry.angle (p c) (p b) (p x) +
      EuclideanGeometry.angle (p y) (p b) (p z) +
      EuclideanGeometry.angle (p b) (p c) (p y) +
      EuclideanGeometry.angle (p x) (p c) (p z)
      < lam := by
  nlinarith

/-- Exact terminal reduction: a proof of the five-point four-angle budget
immediately rules out the Hamiltonian residual. -/
theorem no_hamiltonian_residual_of_four_angle_budget
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    {b c x y z : V}
    (hB :
      EuclideanGeometry.angle (p c) (p b) (p x) +
          EuclideanGeometry.angle (p y) (p b) (p z)
        ≤ delta * lam)
    (hC :
      EuclideanGeometry.angle (p b) (p c) (p y) +
          EuclideanGeometry.angle (p x) (p c) (p z)
        ≤ delta * lam)
    (hbudget :
      HamiltonianFourAngleBudget p lam b c x y z) :
    False := by
  have hlt :=
    hamiltonian_residual_four_angle_sum_lt
      (p := p) hdeltaHalf hlam hB hC
  exact (not_lt_of_ge hbudget) hlt

#print axioms hamiltonian_residual_four_angle_sum_lt
#print axioms no_hamiltonian_residual_of_four_angle_budget

end JSP000404Research
