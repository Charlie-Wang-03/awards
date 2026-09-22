import JSP000404Research.SharpOuterAngles
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Complement clusters around a distinguished sharp centre

Fix a distinguished centre s.  Say that another centre i has a
SharpComplementCluster if every angle at i formed by two vertices different
from both i and s is at most delta*lambda.

For a support-two deficit-two centre in the presence of a sharp centre, the
intended geometric bridge is that the two positive quotient gaps isolate the
ray to s, while all remaining zero-quotient gaps have total width at most
delta/t.  Hence all non-s rays form exactly such a narrow complement cluster.

This file isolates the global consequence of that bridge.

If two distinct centres i,j both have narrow complement clusters relative to
the same s and there is a fourth vertex k, then triangle i-j-k has angles at i
and j at most delta*lambda.  The global cap bounds the angle at k by
pi-lambda.  Since 2*delta<1, the three angles cannot sum to pi.

Thus, once the local support-two -> complement-cluster bridge is supplied,
there can be at most one support-two deficit-two centre around a sharp centre
in every configuration with at least four points.
-/

namespace JSP000404Research

open Real

def SharpComplementClusterAt
    {V : Type*} (p : V → Plane)
    (s i : V) (delta lam : ℝ) : Prop :=
  ∀ j k : V,
    j ≠ i →
    k ≠ i →
    j ≠ k →
    j ≠ s →
    k ≠ s →
    EuclideanGeometry.angle (p j) (p i) (p k) ≤
      delta * lam

theorem no_two_complement_clusters_with_fourth
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {delta lam : ℝ}
    (hdelta : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {s i j k : V}
    (hsi : s ≠ i)
    (hsj : s ≠ j)
    (hsk : s ≠ k)
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k)
    (hi : SharpComplementClusterAt p s i delta lam)
    (hj : SharpComplementClusterAt p s j delta lam) :
    False := by
  have hangleI :
      EuclideanGeometry.angle (p j) (p i) (p k) ≤
        delta * lam :=
    hi j k hij.symm hik hjk hsj.symm hsk.symm
  have hangleJ :
      EuclideanGeometry.angle (p i) (p j) (p k) ≤
        delta * lam :=
    hj i k hij hik hjk hsi.symm hsk.symm
  have hangleK :
      EuclideanGeometry.angle (p i) (p k) (p j) ≤
        Real.pi - lam :=
    hcap i k j hik hjk hij
  have hsum :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p i) (p₂ := p j) (p k)
      (hp.ne hij)
  have hcomm :
      EuclideanGeometry.angle (p k) (p i) (p j) =
        EuclideanGeometry.angle (p j) (p i) (p k) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcomm] at hsum
  nlinarith

#print axioms no_two_complement_clusters_with_fourth

end JSP000404Research
