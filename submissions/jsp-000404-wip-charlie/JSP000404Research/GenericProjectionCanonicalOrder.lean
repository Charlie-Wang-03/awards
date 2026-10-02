import JSP000404Research.GenericProjectionOrder
import JSP000404Research.ProjectionOrderedVertices
import JSP000404Research.CanonicalSignOrder
import Mathlib.Tactic

/-!
# Generic projection order agrees with the canonical planar order

The explicit generic projection slope is

  a* = 1 + sum_{b in badProjectionSlopes p} |b|.

Hence it strictly dominates the absolute value of every pairwise bad slope.
For a displacement in the canonical positive half-plane

  dy > 0  or  (dy = 0 and dx > 0),

this forces dx + a* dy > 0.  Thus canonical planar order implies strict
generic-projection order.  Since both orders are total on an injective finite
configuration, they coincide.

This bridge lets the residual Q/T/T/T order-rigidity lemmas and the canonical
sign/side lemmas operate on the same four-point order.
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
  rcases huv with hy | ⟨hy,hx⟩
  · have hdy :
        0 < p v 1 - p u 1 := by
      simpa using hy
    have hs :=
      genericProjectionSlope_gt_abs_pairBad p u v
    have hbad :
        pairBadProjectionSlope p u v =
          -(p v 0 - p u 0) / (p v 1 - p u 1) := by
      unfold pairBadProjectionSlope
      have hden :
          p u 1 - p v 1 = -(p v 1 - p u 1) := by
        ring
      rw [hden]
      field_simp [ne_of_gt hdy]
      ring
    rw [hbad] at hs
    have hle :
        -(p v 0 - p u 0) / (p v 1 - p u 1)
          ≤
        |-(p v 0 - p u 0) / (p v 1 - p u 1)| :=
      le_abs_self _
    have hlt :
        -(p v 0 - p u 0) / (p v 1 - p u 1)
          < genericProjectionSlope p :=
      hle.trans_lt hs
    have hmul :
        -(p v 0 - p u 0) <
          genericProjectionSlope p * (p v 1 - p u 1) := by
      exact (div_lt_iff₀ hdy).mp hlt
    linarith
  · have hdy :
        p v 1 - p u 1 = 0 := by
      simpa using sub_eq_zero.mpr hy
    have hdx :
        0 < p v 0 - p u 0 := by
      simpa using hx
    linarith

namespace ProjectionOrdered

theorem canonicalPointLt_iff_projection_lt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (u v : ProjectionOrdered V) :
    CanonicalPointLt p u.toOriginal v.toOriginal
      ↔
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
      exact huv (toOriginal_injective h)
    rcases canonicalPointLt_total_of_ne hp horig with hcanon | hrev
    · exact hcanon
    · have hrevProj :
          @LT.lt (ProjectionOrdered V)
            (projectionLinearOrder hp) v u := by
        rw [lt_iff_projectionCoord_lt hp]
        exact projectionValue_lt_of_canonicalPointLt p hrev
      exact False.elim (lt_asymm hproj hrevProj)

theorem projection_lt_iff_canonicalPointLt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (u v : ProjectionOrdered V) :
    @LT.lt (ProjectionOrdered V)
        (projectionLinearOrder hp) u v
      ↔
    CanonicalPointLt p u.toOriginal v.toOriginal :=
  (canonicalPointLt_iff_projection_lt hp u v).symm

#print axioms projectionValue_lt_of_canonicalPointLt
#print axioms canonicalPointLt_iff_projection_lt

end ProjectionOrdered
end JSP000404Research
