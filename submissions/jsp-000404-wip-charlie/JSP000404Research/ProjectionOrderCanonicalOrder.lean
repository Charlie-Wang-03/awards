import JSP000404Research.ProjectionOrderedVertices
import JSP000404Research.CanonicalSignOrder
import Mathlib.Tactic

/-!
# Generic projection order equals the canonical planar order

The explicit generic slope is not merely non-bad.  It is

  1 + sum |bad slope|,

so it is strictly larger than the absolute value of every pairwise bad slope.

Consequently the projection functional

  L(x,y) = x + a_* y

orders every non-horizontal pair by the sign of its y-difference.  Horizontal
pairs are ordered by x.  This is exactly CanonicalPointLt, whose positive
half-plane is lexicographic in (y,x).

Thus the ProjectionOrdered linear order and the canonical planar order agree
on every pair.
-/

namespace JSP000404Research

theorem genericProjectionSlope_gt_abs_pairBad
    {V : Type*} [Fintype V]
    (p : V → Plane)
    (i j : V) :
    |pairBadProjectionSlope p i j| <
      genericProjectionSlope p := by
  classical
  have hmem :
      pairBadProjectionSlope p i j ∈ badProjectionSlopes p :=
    pairBadProjectionSlope_mem p i j
  have hle :
      |pairBadProjectionSlope p i j| ≤
        ∑ b ∈ badProjectionSlopes p, |b| := by
    exact Finset.single_le_sum
      (fun b _ => abs_nonneg b) hmem
  unfold genericProjectionSlope
  linarith

theorem canonicalPointLt_projectionValue_lt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {i j : V}
    (hij : CanonicalPointLt p i j) :
    projectionValue p (genericProjectionSlope p) i <
      projectionValue p (genericProjectionSlope p) j := by
  unfold CanonicalPointLt PlaneHalfPositive at hij
  unfold projectionValue
  rcases hij with hy | ⟨hy0,hx⟩
  · change 0 < p j 1 - p i 1 at hy
    let dy : ℝ := p j 1 - p i 1
    let dx : ℝ := p j 0 - p i 0
    let a : ℝ := genericProjectionSlope p
    let b : ℝ := pairBadProjectionSlope p i j
    have hdy : 0 < dy := by simpa [dy] using hy
    have hden : p i 1 - p j 1 ≠ 0 := by
      dsimp [dy] at hdy
      linarith
    have hb :
        b = -dx / dy := by
      dsimp [b,dx,dy,pairBadProjectionSlope]
      field_simp [hden]
      ring
    have habs :
        |b| < a := by
      simpa [a,b] using
        genericProjectionSlope_gt_abs_pairBad p i j
    have hba : b < a := lt_of_le_of_lt (le_abs_self b) habs
    have hinc :
        0 < dx + a * dy := by
      rw [hb] at hba
      have hdy0 : dy ≠ 0 := ne_of_gt hdy
      field_simp [hdy0] at hba
      nlinarith
    dsimp [dx,dy,a] at hinc
    linarith
  · change p j 1 - p i 1 = 0 at hy0
    change 0 < p j 0 - p i 0 at hx
    nlinarith

namespace ProjectionOrdered

theorem canonicalPointLt_iff_projection_lt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (u v : ProjectionOrdered V) :
    CanonicalPointLt p u.toOriginal v.toOriginal ↔
      @LT.lt (ProjectionOrdered V) (projectionLinearOrder hp) u v := by
  constructor
  · intro hcan
    rw [lt_iff_projectionCoord_lt hp]
    exact canonicalPointLt_projectionValue_lt hcan
  · intro huv
    have hne : u.toOriginal ≠ v.toOriginal := by
      intro h
      apply (ne_of_lt huv)
      apply toOriginal_injective
      exact h
    rcases canonicalPointLt_total_of_ne hp hne with hcan | hrev
    · exact hcan
    · have hvult :
          @LT.lt (ProjectionOrdered V)
            (projectionLinearOrder hp) v u := by
        rw [lt_iff_projectionCoord_lt hp]
        exact canonicalPointLt_projectionValue_lt hrev
      exact False.elim (lt_asymm huv hvult)

theorem projection_lt_iff_canonicalPointLt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (u v : ProjectionOrdered V) :
    @LT.lt (ProjectionOrdered V) (projectionLinearOrder hp) u v ↔
      CanonicalPointLt p u.toOriginal v.toOriginal :=
  (canonicalPointLt_iff_projection_lt hp u v).symm

#print axioms canonicalPointLt_iff_projection_lt
#print axioms projection_lt_iff_canonicalPointLt

end ProjectionOrdered

#print axioms genericProjectionSlope_gt_abs_pairBad
#print axioms canonicalPointLt_projectionValue_lt

end JSP000404Research
