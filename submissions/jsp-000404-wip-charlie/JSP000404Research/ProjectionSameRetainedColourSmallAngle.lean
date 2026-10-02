import JSP000404Research.ProjectionLocalDirectionValue
import JSP000404Research.CutBandSmallAngle
import JSP000404Research.StandardResidual
import JSP000404Research.ResidualLists
import Mathlib.Tactic

/-!
# Same standard residual colour gives a genuine small angle

For the generic projection DirectionData, the local direction coordinate at a
centre is exactly the normalized projective-cut ray coordinate.  Consequently
two incident retained edges carrying the same standard residual colour lie in
the same unit cut band, and their genuine Euclidean angle is strictly less
than lambda.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

def IncidentRetainedColour
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (i x : V) (c : Fin n) : Prop :=
  (∃ hix : i < x,
      ∃ hret : (C.color i x).val < n,
        retainedColor C i x hret = c)
  ∨
  (∃ hxi : x < i,
      ∃ hret : (C.color x i).val < n,
        retainedColor C x i hret = c)

theorem genericLocalDirectionValue_eq_projectionCutNormalized
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (j : OtherVertex i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i j
      =
    cutNormalizedRayTheta
      (reindexedPoint_injective hp) t
      (projectionProjectiveCut p) i j := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  rw [genericLocalDirectionValue_eq_cutRotate
      hp hcap ht hlam i j]
  rw [cutNormalizedRayTheta_eq_div_lam
      (reindexedPoint_injective hp) ht hlam i j]
  unfold cutRayTheta
  rfl

theorem incidentRetainedColour_local_band
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i x : ProjectionOrdered V}
    {c : Fin n}
    (hix : i ≠ x)
    (hc :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      IncidentRetainedColour R i x c) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let D := genericDirectionData_sendov hp hcap
      (sendov_scale_pos hn hdelta0 ht) hlam
    let j : OtherVertex i := ⟨x,hix.symm⟩
    (c.val : ℝ) ≤ D.localDirectionValue i j ∧
      D.localDirectionValue i j < (c.val : ℝ) + 1 := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t := sendov_scale_pos hn hdelta0 ht
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidth : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let R := DirectionData.standardResidualColoring D n hwidth
  let j : OtherVertex i := ⟨x,hix.symm⟩
  have hc' : IncidentRetainedColour R i x c := by
    simpa [R,D,planarStandardResidualColoring] using hc
  rcases hc' with hright | hleft
  · obtain ⟨hixlt,hret,hcol⟩ := hright
    have hfull :
        R.color i x = c.castSucc := by
      apply Fin.ext
      have hv := congrArg Fin.val hcol
      simpa [retainedColor] using hv
    have hb :=
      (DirectionData.standardBandColor_eq_iff
        D (n+1) (Nat.succ_pos n)
        (by exact_mod_cast hwidth)
        hixlt c.castSucc).1
        (by simpa [R,DirectionData.standardResidualColoring] using hfull)
    have hjnot : ¬ x < i := not_lt_of_ge hixlt.le
    simpa [D,j,DirectionData.localDirectionValue,hjnot] using hb
  · obtain ⟨hxilt,hret,hcol⟩ := hleft
    have hfull :
        R.color x i = c.castSucc := by
      apply Fin.ext
      have hv := congrArg Fin.val hcol
      simpa [retainedColor] using hv
    have hb :=
      (DirectionData.standardBandColor_eq_iff
        D (n+1) (Nat.succ_pos n)
        (by exact_mod_cast hwidth)
        hxilt c.castSucc).1
        (by simpa [R,DirectionData.standardResidualColoring] using hfull)
    simpa [D,j,DirectionData.localDirectionValue,hxilt] using hb

theorem actual_angle_lt_lam_of_same_standard_retained_colour
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i x y : ProjectionOrdered V}
    {c : Fin n}
    (hix : i ≠ x)
    (hiy : i ≠ y)
    (hxy : x ≠ y)
    (hx :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      IncidentRetainedColour R i x c)
    (hy :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      IncidentRetainedColour R i y c) :
    EuclideanGeometry.angle
      (reindexedPoint p x) (reindexedPoint p i) (reindexedPoint p y)
      < lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t := sendov_scale_pos hn hdelta0 ht
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let jx : OtherVertex i := ⟨x,hix.symm⟩
  let jy : OtherVertex i := ⟨y,hiy.symm⟩
  have hbx :=
    incidentRetainedColour_local_band
      hp hcap hn hdelta0 hdelta1 ht hlam hix hx
  have hby :=
    incidentRetainedColour_local_band
      hp hcap hn hdelta0 hdelta1 ht hlam hiy hy
  have hcx :
      (c.val : ℝ) ≤
        cutNormalizedRayTheta
          (reindexedPoint_injective hp) t
          (projectionProjectiveCut p) i jx ∧
      cutNormalizedRayTheta
          (reindexedPoint_injective hp) t
          (projectionProjectiveCut p) i jx <
        (c.val : ℝ) + 1 := by
    rw [← genericLocalDirectionValue_eq_projectionCutNormalized
      hp hcap htpos hlam i jx]
    simpa [D,jx] using hbx
  have hcy :
      (c.val : ℝ) ≤
        cutNormalizedRayTheta
          (reindexedPoint_injective hp) t
          (projectionProjectiveCut p) i jy ∧
      cutNormalizedRayTheta
          (reindexedPoint_injective hp) t
          (projectionProjectiveCut p) i jy <
        (c.val : ℝ) + 1 := by
    rw [← genericLocalDirectionValue_eq_projectionCutNormalized
      hp hcap htpos hlam i jy]
    simpa [D,jy] using hby
  have hcut0 : 0 ≤ projectionProjectiveCut p :=
    projectionProjectiveCut_nonneg p
  have hcutpi : projectionProjectiveCut p < Real.pi :=
    projectionProjectiveCut_lt_pi p
  have hjxy : jx ≠ jy := by
    intro h
    apply hxy
    exact congrArg Subtype.val h
  simpa [jx,jy,reindexedPoint] using
    actual_angle_lt_lam_of_same_cut_band
      (reindexedPoint_injective hp)
      (by
        intro a b c hab hac hbc
        exact hcap a.toOriginal b.toOriginal c.toOriginal
          (by intro h; apply hab; exact ProjectionOrdered.toOriginal_injective h)
          (by intro h; apply hac; exact ProjectionOrdered.toOriginal_injective h)
          (by intro h; apply hbc; exact ProjectionOrdered.toOriginal_injective h))
      htpos hlam hcut0 hcutpi
      i jx jy hjxy
      hcx.1 hcx.2 hcy.1 hcy.2

#print axioms genericLocalDirectionValue_eq_projectionCutNormalized
#print axioms actual_angle_lt_lam_of_same_standard_retained_colour

end ProjectionOrdered
end JSP000404Research
