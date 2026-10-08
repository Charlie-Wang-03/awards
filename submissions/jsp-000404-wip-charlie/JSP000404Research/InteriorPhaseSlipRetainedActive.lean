import JSP000404Research.InteriorPhaseSlipRayWitness
import JSP000404Research.PlanarCompletionDefectBalance
import Mathlib.Tactic

/-!
# Adjacent retained Boolean coordinates forced by an interior phase slip

A locally saturated centre with inactive residual top colour has a
consecutive pair of actual incident directions with a unit *integer*
band jump but real direction gap below one.

Because the residual top band n is inactive, both of these endpoint
bands lie below n. Therefore they are two distinct adjacent *retained*
active Boolean coordinates in the n-dimensional completion cube.

This delivers explicit retained coordinates to the existing flip/hole
outlets; no collision-free matching is claimed.
-/

namespace JSP000404Research
namespace DirectionData
namespace LocalDirectionCycle

open OrderedEdgeColoring

/-- Local tightness + residual inactivity forces TWO CONSECUTIVE
retained active band coordinates. In particular n must be at least 2. -/
theorem exists_adjacent_retained_active_bands_of_tight_inactive
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (htight :
      C.exponent + (D.incidentBands (n + 1) i).card = n + 1)
    (hres : residualCoord n ∉
      active (standardResidualColoring D n
        (by exact_mod_cast ht)) i) :
    ∃ c d : Fin n,
      c.val + 1 = d.val ∧
      c ∈ retainedActive (standardResidualColoring D n
        (by exact_mod_cast ht)) i ∧
      d ∈ retainedActive (standardResidualColoring D n
        (by exact_mod_cast ht)) i := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  obtain ⟨u,v,pre,post,hsegment,hnonneg,hshort,hjump⟩ :=
    C.exists_adjacent_rays_with_short_band_crossing ht htight hres
  have hvNonneg := D.localDirectionValue_nonneg i v
  have hvBelow : D.localDirectionValue i v < ((n+1 : ℕ) : ℝ) := by
    have h := D.localDirectionValue_lt i v
    have htn : t < ((n+1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using ht
    exact h.trans htn
  have hvBound : Nat.floor (D.localDirectionValue i v) ≤ n := by
    have hf := (Nat.floor_lt hvNonneg).2 hvBelow
    omega
  have hvNeTop : Nat.floor (D.localDirectionValue i v) ≠ n := by
    intro heq
    have hband : residualCoord n ∈ D.incidentBands (n+1) i := by
      apply (mem_incidentBands_iff_exists_local_floor
        D (n+1) i (residualCoord n)).2
      exact ⟨v, by simpa [residualCoord] using heq⟩
    have hactive : residualCoord n ∈ active B i := by
      simpa [B, standardResidual_active_eq_incidentBands_succ] using hband
    exact hres hactive
  have hvRet : Nat.floor (D.localDirectionValue i v) < n := by
    omega
  have huRet : Nat.floor (D.localDirectionValue i u) < n := by
    omega
  let c : Fin n :=
    ⟨Nat.floor (D.localDirectionValue i u), huRet⟩
  let d : Fin n :=
    ⟨Nat.floor (D.localDirectionValue i v), hvRet⟩
  have hc : c ∈ retainedActive B i := by
    rw [show retainedActive B i = D.incidentBands n i from
      standardResidual_retainedActive_eq_incidentBands
        D n (by exact_mod_cast ht) i]
    exact (mem_incidentBands_iff_exists_local_floor
      D n i c).2 ⟨u, rfl⟩
  have hd : d ∈ retainedActive B i := by
    rw [show retainedActive B i = D.incidentBands n i from
      standardResidual_retainedActive_eq_incidentBands
        D n (by exact_mod_cast ht) i]
    exact (mem_incidentBands_iff_exists_local_floor
      D n i d).2 ⟨v, rfl⟩
  refine ⟨c,d,?_,?_,?_⟩
  · dsimp [c,d]
    omega
  · simpa only [B] using hc
  · simpa only [B] using hd

#print axioms LocalDirectionCycle.exists_adjacent_retained_active_bands_of_tight_inactive

end LocalDirectionCycle
end DirectionData
end JSP000404Research
