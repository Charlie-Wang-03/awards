import JSP000404Research.ProjectionCutLocalValueBridge
import JSP000404Research.ProjectionCutSignOrder
import JSP000404Research.ResidualSameCodeOrientation
import JSP000404Research.StandardResidual
import Mathlib.Tactic

/-!
# Retained residual bits equal projection-cut band signs

For the generic-projection standard residual colouring, every retained active
coordinate c is the same unit band in the local DirectionData coordinate and
in the projection-cut normalized ray coordinate.

The retained bit says whether that band is represented by an incoming edge.
At the distinguished projection cut, cutRaySign is true exactly for an
incoming ray and false exactly for an outgoing ray.  Hence the two Boolean
labels agree.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem standardResidual_retainedBit_eq_cutProjectiveBandBit
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn1 : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (c : Fin n) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t :=
      sendov_scale_pos hn1 hdelta0 ht
    let hwidth : t < (n + 1 : ℕ) := by
      rw [ht]
      exact_mod_cast (show delta < (1 : ℝ) from hdelta1)
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let R := standardResidualColoring D n hwidth
    retainedBit R i c =
      cutProjectiveBandBit
        (reindexedPoint_injective hp)
        (angleCap_reindexed hcap)
        htpos hlam
        (projectionProjectiveCut_pos p).le
        (projectionProjectiveCut_lt_pi p)
        n i c.castSucc := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t :=
    sendov_scale_pos hn1 hdelta0 ht
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidth : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let R := standardResidualColoring D n hwidth
  let cut := projectionProjectiveCut p

  have hiff :
      retainedBit R i c = true ↔
      cutProjectiveBandBit
        (reindexedPoint_injective hp)
        (angleCap_reindexed hcap)
        htpos hlam
        (projectionProjectiveCut_pos p).le
        (projectionProjectiveCut_lt_pi p)
        n i c.castSucc = true := by
    constructor
    · intro hbit
      have hIn :
          c ∈ incomingRetained R i :=
        (mem_incomingRetained_iff_retainedBit_true R i c).2 hbit
      obtain ⟨a,hai,hcol⟩ :=
        (mem_incomingRetained_iff R i c).1 hIn
      let r : OtherVertex i := ⟨a, ne_of_lt hai⟩
      have hbandD :
          (c : ℝ) ≤ D.value a i ∧
          D.value a i < (c : ℝ) + 1 := by
        have h :=
          (standardBandColor_eq_iff
            D (n + 1) (Nat.succ_pos n)
            (by exact_mod_cast hwidth)
            hai c.castSucc).1
            (by simpa [R,standardResidualColoring] using hcol)
        simpa using h
      have hlocal :
          D.localDirectionValue i r = D.value a i := by
        simp [DirectionData.localDirectionValue,r,hai]
      have hcutLocal :=
        genericLocalDirectionValue_eq_cutNormalizedRayTheta
          hp hcap htpos hlam i r
      have hcutBand :
          RayInCutProjectiveBand
            (reindexedPoint_injective hp) t cut i r c.castSucc := by
        unfold RayInCutProjectiveBand
        rw [← hcutLocal, hlocal]
        simpa using hbandD
      have hsign :
          cutRaySign
            (reindexedPoint_injective hp) cut i r = true := by
        simpa [cut,r] using
          cutRaySign_projectionCut_eq_true_of_gt hp hai
      have hex :
          ∃ r' : OtherVertex i,
            RayInCutProjectiveBand
              (reindexedPoint_injective hp) t cut i r' c.castSucc ∧
            cutRaySign
              (reindexedPoint_injective hp) cut i r' = true :=
        ⟨r,hcutBand,hsign⟩
      simp [cutProjectiveBandBit,cut,hex]
    · intro hcutBit
      have hex :
          ∃ r : OtherVertex i,
            RayInCutProjectiveBand
              (reindexedPoint_injective hp) t cut i r c.castSucc ∧
            cutRaySign
              (reindexedPoint_injective hp) cut i r = true := by
        simpa [cutProjectiveBandBit,cut] using hcutBit
      obtain ⟨r,hrBand,hrSign⟩ := hex
      have hri : r.1 < i := by
        rcases lt_or_gt_of_ne r.2 with hri | hir
        · exact hri
        · have hfalse :
            cutRaySign
              (reindexedPoint_injective hp) cut i r = false := by
            simpa [cut,r] using
              cutRaySign_projectionCut_eq_false_of_lt hp hir
          rw [hfalse] at hrSign
          simp at hrSign
      have hlocal :=
        genericLocalDirectionValue_eq_cutNormalizedRayTheta
          hp hcap htpos hlam i r
      have hlocalValue :
          D.localDirectionValue i r = D.value r.1 i := by
        simp [DirectionData.localDirectionValue,hri]
      have hbandD :
          (c : ℝ) ≤ D.value r.1 i ∧
          D.value r.1 i < (c : ℝ) + 1 := by
        unfold RayInCutProjectiveBand at hrBand
        rw [← hcutLocal, hlocalValue] at hrBand
        simpa using hrBand
      have hcol :
          R.color r.1 i = c.castSucc := by
        have h :=
          (standardBandColor_eq_iff
            D (n + 1) (Nat.succ_pos n)
            (by exact_mod_cast hwidth)
            hri c.castSucc).2
            (by simpa using hbandD)
        simpa [R,standardResidualColoring] using h
      have hIn :
          c ∈ incomingRetained R i :=
        (mem_incomingRetained_iff R i c).2
          ⟨r.1,hri,hcol⟩
      exact
        (mem_incomingRetained_iff_retainedBit_true R i c).1 hIn

  cases hR : retainedBit R i c <;>
    cases hC :
      cutProjectiveBandBit
        (reindexedPoint_injective hp)
        (angleCap_reindexed hcap)
        htpos hlam
        (projectionProjectiveCut_pos p).le
        (projectionProjectiveCut_lt_pi p)
        n i c.castSucc <;>
    simp_all

#print axioms standardResidual_retainedBit_eq_cutProjectiveBandBit

end ProjectionOrdered
end JSP000404Research
