import JSP000404Research.HamiltonianResidualBudget
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# Transversal-angle ordering in the Hamiltonian residual

Write

  A = angle(c,b,x),   B = angle(y,b,z),
  C = angle(b,c,y),   D = angle(x,c,z),

and let

  X = angle(b,x,c),   Y = angle(b,y,c),   Z = angle(b,z,c)

be the three angles under which x,y,z see the base segment bc.

Triangle sums and two angular triangle inequalities give the exact robust
estimate

  pi - (A+B+C+D) <= X + Y - Z.

In the Hamiltonian residual, A+B+C+D <= 2*delta*lambda.  Hence in the lower
branch delta<1/2,

  pi-lambda < X+Y-Z.

The global cap X,Y <= pi-lambda then forces

  Z < X  and  Z < Y.

Thus z is a strict minimum of the three base-subtended angles.  This is a new
geometric rigidity of the surviving matching terminal.
-/

namespace JSP000404Research

open Real

theorem four_angle_transversal_lower_bound
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {b c x y z : V}
    (hbc : b ≠ c)
    (hbx : b ≠ x) (hcx : c ≠ x)
    (hby : b ≠ y) (hcy : c ≠ y)
    (hbz : b ≠ z) (hcz : c ≠ z) :
    Real.pi -
      (EuclideanGeometry.angle (p c) (p b) (p x) +
       EuclideanGeometry.angle (p y) (p b) (p z) +
       EuclideanGeometry.angle (p b) (p c) (p y) +
       EuclideanGeometry.angle (p x) (p c) (p z))
      ≤
      EuclideanGeometry.angle (p b) (p x) (p c) +
      EuclideanGeometry.angle (p b) (p y) (p c) -
      EuclideanGeometry.angle (p b) (p z) (p c) := by
  have hsumX :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p c) (p₂ := p b) (p x)
      (hp.ne hbc)
  have hsumY :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p b) (p₂ := p c) (p y)
      (hp.ne hbc.symm)
  have hsumZ :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p b) (p₂ := p c) (p z)
      (hp.ne hbc.symm)

  have hcommEX :
      EuclideanGeometry.angle (p x) (p c) (p b) =
        EuclideanGeometry.angle (p b) (p c) (p x) :=
    EuclideanGeometry.angle_comm _ _ _
  have hcommFX :
      EuclideanGeometry.angle (p y) (p b) (p c) =
        EuclideanGeometry.angle (p c) (p b) (p y) :=
    EuclideanGeometry.angle_comm _ _ _
  have hcommZY :
      EuclideanGeometry.angle (p c) (p y) (p b) =
        EuclideanGeometry.angle (p b) (p y) (p c) :=
    EuclideanGeometry.angle_comm _ _ _
  have hcommZZ :
      EuclideanGeometry.angle (p c) (p z) (p b) =
        EuclideanGeometry.angle (p b) (p z) (p c) :=
    EuclideanGeometry.angle_comm _ _ _
  have hcommG :
      EuclideanGeometry.angle (p z) (p b) (p c) =
        EuclideanGeometry.angle (p c) (p b) (p z) :=
    EuclideanGeometry.angle_comm _ _ _

  rw [hcommEX] at hsumX
  rw [hcommZY, hcommFX] at hsumY
  rw [hcommZZ, hcommG] at hsumZ

  have hpathB :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p b) (p c) (p z) (p y)
  have hcommB :
      EuclideanGeometry.angle (p z) (p b) (p y) =
        EuclideanGeometry.angle (p y) (p b) (p z) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommB] at hpathB

  have hpathC :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p c) (p b) (p z) (p x)
  have hcommD :
      EuclideanGeometry.angle (p z) (p c) (p x) =
        EuclideanGeometry.angle (p x) (p c) (p z) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommD] at hpathC

  linarith

theorem hamiltonian_residual_transversal_strict
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    {b c x y z : V}
    (hbc : b ≠ c)
    (hbx : b ≠ x) (hcx : c ≠ x)
    (hby : b ≠ y) (hcy : c ≠ y)
    (hbz : b ≠ z) (hcz : c ≠ z)
    (hB :
      EuclideanGeometry.angle (p c) (p b) (p x) +
          EuclideanGeometry.angle (p y) (p b) (p z)
        ≤ delta * lam)
    (hC :
      EuclideanGeometry.angle (p b) (p c) (p y) +
          EuclideanGeometry.angle (p x) (p c) (p z)
        ≤ delta * lam) :
    Real.pi - lam <
      EuclideanGeometry.angle (p b) (p x) (p c) +
      EuclideanGeometry.angle (p b) (p y) (p c) -
      EuclideanGeometry.angle (p b) (p z) (p c) := by
  have hfour :=
    four_angle_transversal_lower_bound
      hp hbc hbx hcx hby hcy hbz hcz
  have hsmall :
      EuclideanGeometry.angle (p c) (p b) (p x) +
        EuclideanGeometry.angle (p y) (p b) (p z) +
        EuclideanGeometry.angle (p b) (p c) (p y) +
        EuclideanGeometry.angle (p x) (p c) (p z)
        ≤ 2 * delta * lam := by
    linarith
  nlinarith

theorem hamiltonian_residual_z_strictly_smallest_base_angle
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    {b c x y z : V}
    (hbc : b ≠ c)
    (hbx : b ≠ x) (hcx : c ≠ x)
    (hby : b ≠ y) (hcy : c ≠ y)
    (hbz : b ≠ z) (hcz : c ≠ z)
    (hB :
      EuclideanGeometry.angle (p c) (p b) (p x) +
          EuclideanGeometry.angle (p y) (p b) (p z)
        ≤ delta * lam)
    (hC :
      EuclideanGeometry.angle (p b) (p c) (p y) +
          EuclideanGeometry.angle (p x) (p c) (p z)
        ≤ delta * lam) :
    EuclideanGeometry.angle (p b) (p z) (p c) <
        EuclideanGeometry.angle (p b) (p x) (p c)
      ∧
    EuclideanGeometry.angle (p b) (p z) (p c) <
        EuclideanGeometry.angle (p b) (p y) (p c) := by
  have hstrict :=
    hamiltonian_residual_transversal_strict
      hp hdeltaHalf hlam
      hbc hbx hcx hby hcy hbz hcz hB hC
  have hcapX :
      EuclideanGeometry.angle (p b) (p x) (p c) ≤
        Real.pi - lam :=
    hcap b x c hbx hbc hcx.symm
  have hcapY :
      EuclideanGeometry.angle (p b) (p y) (p c) ≤
        Real.pi - lam :=
    hcap b y c hby hbc hcy.symm
  constructor <;> linarith

#print axioms four_angle_transversal_lower_bound
#print axioms hamiltonian_residual_transversal_strict
#print axioms hamiltonian_residual_z_strictly_smallest_base_angle

end JSP000404Research
