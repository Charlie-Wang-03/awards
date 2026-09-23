
import JSP000404Research.SharpCentre
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# An explicit generic linear projection for a finite planar configuration

For a real parameter a consider

  L_a(x,y) = x + a*y.

For distinct points i,j with different y-coordinates, equality
L_a(p_i)=L_a(p_j) can occur for only one bad slope

  a = (x_j-x_i)/(y_i-y_j).

Horizontal pairs never collide under L_a because injectivity of p forces their
x-coordinates to differ.

There are only finitely many point pairs.  Instead of invoking an abstract
"infinite field avoids finite sets" theorem, define the finite bad-slope set S
and choose explicitly

  a_* = 1 + sum_{b in S} |b|.

Every b in S satisfies b <= |b| <= sum |S| < a_*, so a_* is not bad.

Therefore L_{a_*} is injective on the finite configuration.  This supplies the
generic projection needed to linearly order the vertices before constructing a
coherent forward angular lift.
-/

namespace JSP000404Research

noncomputable def projectionValue
    {V : Type*}
    (p : V → Plane) (a : ℝ) (v : V) : ℝ :=
  p v 0 + a * p v 1

noncomputable def pairBadProjectionSlope
    {V : Type*}
    (p : V → Plane) (i j : V) : ℝ :=
  (p j 0 - p i 0) / (p i 1 - p j 1)

noncomputable def badProjectionSlopes
    {V : Type*} [Fintype V]
    (p : V → Plane) : Finset ℝ := by
  classical
  exact ((Finset.univ : Finset V).product Finset.univ).image
    (fun ij => pairBadProjectionSlope p ij.1 ij.2)

theorem pairBadProjectionSlope_mem
    {V : Type*} [Fintype V]
    (p : V → Plane) (i j : V) :
    pairBadProjectionSlope p i j ∈ badProjectionSlopes p := by
  classical
  unfold badProjectionSlopes
  apply Finset.mem_image.mpr
  refine ⟨(i,j), ?_, rfl⟩
  simp

noncomputable def genericProjectionSlope
    {V : Type*} [Fintype V]
    (p : V → Plane) : ℝ :=
  1 + ∑ b ∈ badProjectionSlopes p, |b|

theorem genericProjectionSlope_not_mem
    {V : Type*} [Fintype V]
    (p : V → Plane) :
    genericProjectionSlope p ∉ badProjectionSlopes p := by
  classical
  intro hmem
  have habs :
      |genericProjectionSlope p| ≤
        ∑ b ∈ badProjectionSlopes p, |b| := by
    exact Finset.single_le_sum
      (fun b _ => abs_nonneg b)
      hmem
  have hself :
      genericProjectionSlope p ≤
        |genericProjectionSlope p| :=
    le_abs_self _
  unfold genericProjectionSlope at habs hself
  linarith

theorem projectionValue_ne_of_slope_ne_bad
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    {a : ℝ} {i j : V}
    (hij : i ≠ j)
    (ha :
      a ≠ pairBadProjectionSlope p i j) :
    projectionValue p a i ≠
      projectionValue p a j := by
  intro heq
  by_cases hy : p i 1 = p j 1
  · have hx : p i 0 = p j 0 := by
      unfold projectionValue at heq
      rw [hy] at heq
      linarith
    apply hij
    apply hp
    funext c
    fin_cases c
    · exact hx
    · exact hy
  · have hden :
        p i 1 - p j 1 ≠ 0 :=
      sub_ne_zero.mpr hy
    have hslope :
        a = pairBadProjectionSlope p i j := by
      unfold pairBadProjectionSlope
      apply (eq_div_iff hden).2
      unfold projectionValue at heq
      nlinarith
    exact ha hslope

/-- The explicit generic projection separates all vertices. -/
theorem genericProjectionValue_injective
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p) :
    Function.Injective
      (projectionValue p (genericProjectionSlope p)) := by
  intro i j hij
  by_contra hne
  have hbad :
      genericProjectionSlope p =
        pairBadProjectionSlope p i j := by
    by_contra hslope
    exact projectionValue_ne_of_slope_ne_bad
      hp hne hslope hij
  have hmem :
      genericProjectionSlope p ∈
        badProjectionSlopes p := by
    rw [hbad]
    exact pairBadProjectionSlope_mem p i j
  exact genericProjectionSlope_not_mem p hmem

/-- Every increasing comparison by the generic projection has strictly
positive projection increment.  This is the half-plane orientation condition
needed by the future forward-angle lift. -/
theorem projection_difference_pos_of_value_lt
    {V : Type*}
    (p : V → Plane) (a : ℝ)
    {i j : V}
    (hij :
      projectionValue p a i <
        projectionValue p a j) :
    0 <
      (p j 0 - p i 0) +
        a * (p j 1 - p i 1) := by
  unfold projectionValue at hij
  linarith

#print axioms genericProjectionSlope_not_mem
#print axioms projectionValue_ne_of_slope_ne_bad
#print axioms genericProjectionValue_injective
#print axioms projection_difference_pos_of_value_lt

end JSP000404Research
