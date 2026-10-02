import JSP000404Research.ProjectionOrderedVertices
import JSP000404Research.CanonicalSignOrder
import Mathlib.Tactic

/-!
# Generic projection order equals the canonical planar order

The explicit generic projection slope is

  a* = 1 + sum_{b in badProjectionSlopes p} |b|.

Hence it strictly dominates the absolute value of every pairwise bad slope.
For a displacement (dx,dy) in the canonical positive half-plane

  dy > 0, or dy = 0 and dx > 0,

this domination forces dx + a* dy > 0.  Therefore canonical planar order
implies generic-projection order.  Injectivity then upgrades this to an iff.

This identifies the two linear orders used by the geometric and residual
parts of the JSP-000404 proof.
-/

namespace JSP000404Research

theorem genericProjectionSlope_gt_abs_bad
    {V : Type*} [Fintype V]
    (p : V → Plane)
    {b : ℝ}
    (hb : b ∈ badProjectionSlopes p) :
    |b| < genericProjectionSlope p := by
  classical
  have hle :
      |b| ≤ ∑ q ∈ badProjectionSlopes p, |q| := by
    exact Finset.single_le_sum
      (fun q _ => abs_nonneg q) hb
  unfold genericProjectionSlope
  linarith

theorem genericProjectionSlope_gt_abs_pairBad
    {V : Type*} [Fintype V]
    (p : V → Plane)
    (u v : V) :
    |pairBadProjectionSlope p u v| <
      genericProjectionSlope p :=
  genericProjectionSlope_gt_abs_bad p
    (pairBadProjectionSlope_mem p u v)

theorem projectionValue_lt_of_canonicalPointLt
    {V : Type*} [Fintype V]
    (p : V → Plane)
    {u v : V}
    (huv : CanonicalPointLt p u v) :
    projectionValue p (genericProjectionSlope p) u <
      projectionValue p (genericProjectionSlope p) v := by
  unfold CanonicalPointLt PlaneHalfPositive at huv
  unfold projectionValue
  rcases huv with hypos | ⟨hyeq,hxpos⟩
  · let dx : ℝ := p v 0 - p u 0
    let dy : ℝ := p v 1 - p u 1
    have hdy : 0 < dy := by
      simpa [dy, sub_apply] using hypos
    have hbad :
        pairBadProjectionSlope p u v = -dx / dy := by
      unfold pairBadProjectionSlope
      dsimp [dx,dy]
      have hden :
          p u 1 - p v 1 = -(p v 1 - p u 1) := by ring
      rw [hden]
      field_simp [ne_of_gt hdy]
      ring
    have hslope :=
      genericProjectionSlope_gt_abs_pairBad p u v
    rw [hbad] at hslope
    have hle :
        -dx / dy ≤ |-dx / dy| :=
      le_abs_self _
    have hgt :
        -dx / dy < genericProjectionSlope p :=
      hle.trans_lt hslope
    have hmul :
        -dx < genericProjectionSlope p * dy := by
      exact (div_lt_iff₀ hdy).mp
        (by simpa [div_eq_mul_inv] using hgt)
    dsimp [dx,dy] at hmul
    linarith
  · have hy :
        p v 1 - p u 1 = 0 := by
      simpa [sub_apply] using sub_eq_zero.mpr hyeq
    have hx :
        0 < p v 0 - p u 0 := by
      simpa [sub_apply] using hxpos
    linarith

namespace ProjectionOrdered

theorem canonicalPointLt_iff_projection_lt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (u v : ProjectionOrdered V) :
    CanonicalPointLt p u.toOriginal v.toOriginal ↔
      @LT.lt (ProjectionOrdered V)
        (projectionLinearOrder hp) u v := by
  constructor
  · intro hcanon
    rw [lt_iff_projectionCoord_lt hp]
    exact projectionValue_lt_of_canonicalPointLt p hcanon
  · intro hproj
    have huv : u ≠ v := ne_of_lt hproj
    have horig :
        u.toOriginal ≠ v.toOriginal := by
      intro h
      apply huv
      exact toOriginal_injective h
    rcases canonicalPointLt_total_of_ne hp horig with hcanon | hreverse
    · exact hcanon
    · have hrevProj :
          @LT.lt (ProjectionOrdered V)
            (projectionLinearOrder hp) v u := by
        rw [lt_iff_projectionCoord_lt hp]
        exact projectionValue_lt_of_canonicalPointLt p hreverse
      exact False.elim (lt_asymm hproj hrevProj)

theorem projection_lt_iff_canonicalPointLt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (u v : ProjectionOrdered V) :
    @LT.lt (ProjectionOrdered V)
        (projectionLinearOrder hp) u v ↔
      CanonicalPointLt p u.toOriginal v.toOriginal :=
  (canonicalPointLt_iff_projection_lt hp u v).symm

#print axioms projectionValue_lt_of_canonicalPointLt
#print axioms canonicalPointLt_iff_projection_lt

end ProjectionOrdered
end JSP000404Research
