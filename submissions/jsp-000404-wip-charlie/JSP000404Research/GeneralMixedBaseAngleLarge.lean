import JSP000404Research.GeneralMixedLargeAngleWitness
import JSP000404Research.GeneralMixedExteriorActualHull
import JSP000404Research.TriangleConvexCone
import Mathlib.Tactic

/-!
# Genuine mixed pattern: the large angle is already present in the base triangle

For points x,y in the triangle conv{s,a,b}, their mutual angle at b is
at most the base opening angle(s,b,a). This uses two triangle inequalities
and the exact convex-cone angle splitting at b, not any assumed angular
ordering or unproved geometric payment.

The actual arbitrary-finite mixed support-one/support-two witness at b
therefore forces angle(s,b,a) >= (n-1)*lambda. This locates the LARGE
ANGULAR DIAMETER at the distinguished base pair even when the particular
large-quotient consecutive endpoints are unrelated interior vertices.

It does NOT establish the residual global six-source dyadic payment.
-/

namespace JSP000404Research

theorem angle_in_triangle_at_vertex_le_base_angle
    (s a b x y : Plane)
    (hx : x ∈ convexHull ℝ ({s, a, b} : Set Plane))
    (hy : y ∈ convexHull ℝ ({s, a, b} : Set Plane))
    (hxb : x ≠ b)
    (hyb : y ≠ b) :
    EuclideanGeometry.angle x b y ≤
      EuclideanGeometry.angle s b a := by
  have hxSplit :
      EuclideanGeometry.angle s b a =
        EuclideanGeometry.angle s b x +
          EuclideanGeometry.angle x b a :=
    angle_split_at_third_of_mem_convexHull_three hx hxb
  have hySplit :
      EuclideanGeometry.angle s b a =
        EuclideanGeometry.angle s b y +
          EuclideanGeometry.angle y b a :=
    angle_split_at_third_of_mem_convexHull_three hy hyb
  have hViaS :
      EuclideanGeometry.angle x b y ≤
        EuclideanGeometry.angle s b x +
          EuclideanGeometry.angle s b y := by
    have h := EuclideanGeometry.angle_le_angle_add_angle b x s y
    simpa only [EuclideanGeometry.angle_comm x b s] using h
  have hViaA :
      EuclideanGeometry.angle x b y ≤
        EuclideanGeometry.angle x b a +
          EuclideanGeometry.angle y b a := by
    have h := EuclideanGeometry.angle_le_angle_add_angle b x a y
    simpa only [EuclideanGeometry.angle_comm a b y] using h
  by_cases hsum :
      EuclideanGeometry.angle s b x +
        EuclideanGeometry.angle s b y ≤
          EuclideanGeometry.angle s b a
  · exact hViaS.trans hsum
  · have hrest :
        EuclideanGeometry.angle x b a +
          EuclideanGeometry.angle y b a ≤
            EuclideanGeometry.angle s b a := by
      linarith
    exact hViaA.trans hrest

/-- Every actual centre, not just a chosen fourth centre, lies in the
mixed-pattern base triangle. The endpoint cases are vertices of the triangle;
all others use the already proved arbitrary-cardinality exterior exclusion. -/
theorem general_mixed_every_vertex_in_base_triangle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2) :
    ∀ c : V, c ≠ b →
      p c ∈ convexHull ℝ ({p s, p a, p b} : Set Plane) := by
  intro c hcb
  by_cases hcs : c = s
  · subst c
    exact (subset_convexHull ℝ ({p s, p a, p b} : Set Plane)) (by simp)
  · by_cases hca : c = a
    · subst c
      exact (subset_convexHull ℝ ({p s, p a, p b} : Set Plane)) (by simp)
    · exact mixed_fourth_mem_triangle_of_actual_pattern
        hp hcap hn hdelta0 hdeltaHalf ht hlam
        hsa hsb (Ne.symm hcs) hab (Ne.symm hca) (Ne.symm hcb)
        Cs Ca Cb hS hA hB hsupA hsupB

/-- A real large quotient angle in the mixed support-two cycle must force
the base wedge itself to be at least (n-1)*lambda. No witness endpoint
identification or extra geometric hypotheses are needed. -/
theorem general_mixed_base_angle_large_of_actual_pattern
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2) :
    (((n - 1 : ℕ) : ℝ) * lam) ≤
      EuclideanGeometry.angle (p s) (p b) (p a) := by
  obtain ⟨x, y, hxy, hlarge⟩ :=
    general_mixed_actual_large_angle_exists
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hab Cs Ca Cb hS hA hB hsupA hsupB
  have hall :=
    general_mixed_every_vertex_in_base_triangle
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hab Cs Ca Cb hS hA hB hsupA hsupB
  have hx := hall x.1 x.2
  have hy := hall y.1 y.2
  exact hlarge.trans
    (angle_in_triangle_at_vertex_le_base_angle
      (p s) (p a) (p b) (p x.1) (p y.1)
      hx hy (hp.ne x.2) (hp.ne y.2))

#print axioms angle_in_triangle_at_vertex_le_base_angle
#print axioms general_mixed_every_vertex_in_base_triangle
#print axioms general_mixed_base_angle_large_of_actual_pattern

end JSP000404Research
