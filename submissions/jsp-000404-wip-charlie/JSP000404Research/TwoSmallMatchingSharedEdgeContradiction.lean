import JSP000404Research.TwoSmallAngleContradiction
import Mathlib.Tactic

/-!
# Shared-edge contradiction for two small perfect matchings

Suppose two distinct centres b,c on a five-vertex configuration carry small
perfect matchings on the other four vertices.

If the two matchings share one matched edge {u,v}, then the remaining unmatched
vertex x must pair with c at b and with b at c.  The two matching-sum bounds

  angle(u,b,v) + angle(c,b,x) <= delta*lambda,
  angle(u,c,v) + angle(b,c,x) <= delta*lambda

force both angles of triangle b-c-x at b and c to be at most delta*lambda.
For delta<1/2 this contradicts the global cap angle<=pi-lambda.

This file packages only the Euclidean core; the finite matching classification
is handled separately.
-/

namespace JSP000404Research

theorem impossible_shared_edge_two_small_matchings
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {delta lam : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    {b c u v x : V}
    (hbc : b ≠ c)
    (hbx : b ≠ x)
    (hcx : c ≠ x)
    (huvB :
      EuclideanGeometry.angle (p u) (p b) (p v) +
        EuclideanGeometry.angle (p c) (p b) (p x)
        ≤ delta * lam)
    (huvC :
      EuclideanGeometry.angle (p u) (p c) (p v) +
        EuclideanGeometry.angle (p b) (p c) (p x)
        ≤ delta * lam) :
    False := by
  have hA0 :
      0 ≤ EuclideanGeometry.angle (p u) (p b) (p v) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hB0 :
      0 ≤ EuclideanGeometry.angle (p u) (p c) (p v) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hsmallB :
      EuclideanGeometry.angle (p c) (p b) (p x)
        ≤ delta * lam := by
    linarith
  have hsmallC :
      EuclideanGeometry.angle (p b) (p c) (p x)
        ≤ delta * lam := by
    linarith
  exact impossible_two_delta_small_angles_under_cap
    hp hcap hdeltaHalf hlam
    hbc hbx hcx
    hsmallB hsmallC

/-- Symmetric presentation where the shared edge is the second matching edge
at one or both centres. -/
theorem impossible_shared_edge_two_small_matchings_symm
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {delta lam : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    {b c u v x : V}
    (hbc : b ≠ c)
    (hbx : b ≠ x)
    (hcx : c ≠ x)
    (hB :
      EuclideanGeometry.angle (p c) (p b) (p x) +
        EuclideanGeometry.angle (p u) (p b) (p v)
        ≤ delta * lam)
    (hC :
      EuclideanGeometry.angle (p b) (p c) (p x) +
        EuclideanGeometry.angle (p u) (p c) (p v)
        ≤ delta * lam) :
    False := by
  apply impossible_shared_edge_two_small_matchings
    hp hcap hdelta0 hdeltaHalf hlam
    hbc hbx hcx
  · linarith
  · linarith

#print axioms impossible_shared_edge_two_small_matchings
#print axioms impossible_shared_edge_two_small_matchings_symm

end JSP000404Research
