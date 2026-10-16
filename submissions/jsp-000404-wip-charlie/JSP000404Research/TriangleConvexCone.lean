import JSP000404Research.CentreExponent
import Mathlib.Analysis.Convex.Join
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Triangle convex-hull points split the outer vertex angles

A point c in convexHull {x,y,z} can be written, from the viewpoint of x, as a
nonnegative linear combination of the two edge displacement vectors y-x and
z-x.  Mathlib's equality case for the angle triangle inequality then gives

  angle(y,x,z) = angle(y,x,c) + angle(c,x,z).

The same statement can be reused cyclically at all three outer vertices.  This
is exactly the geometry needed by the mixed four-centre interior terminal.
-/

namespace JSP000404Research

open Real

/-- A point in a triangle lies in the positive displacement cone from each
chosen vertex. -/
theorem sub_mem_nnreal_span_of_mem_convexHull_three
    {x y z c : Plane}
    (hc : c ∈ convexHull ℝ ({x, y, z} : Set Plane)) :
    c - x ∈ Submodule.span NNReal ({y - x, z - x} : Set Plane) := by
  have hc' :
      c ∈ convexJoin ℝ {x} (segment ℝ y z) := by
    rw [convexJoin_singleton_segment]
    exact hc
  obtain ⟨x0, hx0, q, hq, hcseg⟩ :=
    (mem_convexJoin.mp hc')
  have hx0eq : x0 = x := by
    simpa using hx0
  subst x0
  rcases hq with ⟨a, b, ha, hb, hab, hqeq⟩
  rcases hcseg with ⟨r, s, hr, hs, hrs, hceq⟩
  rw [Submodule.mem_span_pair]
  let ka : NNReal := ⟨s * a, mul_nonneg hs ha⟩
  let kb : NNReal := ⟨s * b, mul_nonneg hs hb⟩
  refine ⟨ka, kb, ?_⟩
  simp only [NNReal.smul_def]
  change ((s * a : ℝ) • (y - x) + (s * b : ℝ) • (z - x) = c - x)
  rw [← hceq, ← hqeq]
  module_nf
  have hab' : b = 1 - a := by linarith
  have hrs' : r = 1 - s := by linarith
  rw [hab', hrs']
  module_nf

/-- Affine angle splitting at one outer vertex of a triangle. -/
theorem angle_split_of_mem_convexHull_three
    {x y z c : Plane}
    (hc : c ∈ convexHull ℝ ({x, y, z} : Set Plane))
    (hcx : c ≠ x) :
    EuclideanGeometry.angle y x z =
      EuclideanGeometry.angle y x c +
        EuclideanGeometry.angle c x z := by
  have hcone :=
    sub_mem_nnreal_span_of_mem_convexHull_three hc
  have hne : c - x ≠ 0 := sub_ne_zero.mpr hcx
  change
    InnerProductGeometry.angle (y - x) (z - x) =
      InnerProductGeometry.angle (y - x) (c - x) +
        InnerProductGeometry.angle (c - x) (z - x)
  exact
    InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span
      hne hcone

/-- The same convex-hull membership may be reordered to choose any outer
vertex as the cone apex. -/
theorem angle_split_at_second_of_mem_convexHull_three
    {x y z c : Plane}
    (hc : c ∈ convexHull ℝ ({x, y, z} : Set Plane))
    (hcy : c ≠ y) :
    EuclideanGeometry.angle x y z =
      EuclideanGeometry.angle x y c +
        EuclideanGeometry.angle c y z := by
  have heq : ({x, y, z} : Set Plane) = {y, x, z} := by
    ext w
    simp [or_comm, or_left_comm, or_assoc]
  have hc' :
      c ∈ convexHull ℝ ({y, x, z} : Set Plane) := by
    rw [← heq]
    exact hc
  exact angle_split_of_mem_convexHull_three hc' hcy

/-- Third-vertex form. -/
theorem angle_split_at_third_of_mem_convexHull_three
    {x y z c : Plane}
    (hc : c ∈ convexHull ℝ ({x, y, z} : Set Plane))
    (hcz : c ≠ z) :
    EuclideanGeometry.angle x z y =
      EuclideanGeometry.angle x z c +
        EuclideanGeometry.angle c z y := by
  have heq : ({x, y, z} : Set Plane) = {z, x, y} := by
    ext w
    simp [or_comm, or_left_comm, or_assoc]
  have hc' :
      c ∈ convexHull ℝ ({z, x, y} : Set Plane) := by
    rw [← heq]
    exact hc
  exact angle_split_of_mem_convexHull_three hc' hcz

#print axioms sub_mem_nnreal_span_of_mem_convexHull_three
#print axioms angle_split_of_mem_convexHull_three

end JSP000404Research
