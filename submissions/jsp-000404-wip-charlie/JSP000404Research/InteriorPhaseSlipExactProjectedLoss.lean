import JSP000404Research.InteriorPhaseSlipRetainedActive
import JSP000404Research.ResidualProjectedLossCore
import JSP000404Research.WeightedProfileRepair
import Mathlib.Tactic

/-!
# The saturated residual-inactive phase-slip centre has exact projected loss

The residual-inactive hypothesis makes the full active palette identical
to the cast of its retained palette. Hence a saturated (n+1)-band
budget has exactly one more unit in its target exponent than its
retained n-cube free-coordinate count.

The resulting loss is precisely a *full retained completion cube*:
  2^exponent(v) - 2^projectedFree(v) = 2^projectedFree(v),
with zero pointwise profile surplus.

This is the explicit bridge from concrete local phase-slip geometry
to the projectedLossVertices / Boolean completion-defect interface.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If the residual top coordinate is inactive, the complete active
palette is exactly the image of the retained active palette. -/
theorem active_eq_cast_retained_of_residual_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (R : OrderedEdgeColoring V (n + 1))
    (v : V)
    (hres : residualCoord n ∉ active R v) :
    active R v = (retainedActive R v).map Fin.castSuccEmb := by
  classical
  ext c
  constructor
  · intro hc
    have hcSmall : c.val < n := by
      by_contra hnot
      have hcLe : c.val ≤ n := by
        have h := c.isLt
        omega
      have hcTop : c = residualCoord n := by
        apply Fin.ext
        simp only [residualCoord]
        omega
      exact hres (hcTop ▸ hc)
    let d : Fin n := ⟨c.val, hcSmall⟩
    have hdVal : d.castSucc = c := Fin.ext rfl
    have hd : d ∈ retainedActive R v :=
      (castSucc_mem_active_iff_mem_retainedActive R v d).1
        (by simpa only [hdVal] using hc)
    exact Finset.mem_map.mpr ⟨d, hd, by simpa [d]⟩
  · intro hc
    obtain ⟨d, hd, hdc⟩ := Finset.mem_map.mp hc
    have hmem := (castSucc_mem_active_iff_mem_retainedActive R v d).2 hd
    simpa only [hdc] using hmem

/-- Inactive residual means full and retained active palettes have
the same finite cardinality. -/
theorem active_card_eq_retained_of_residual_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (R : OrderedEdgeColoring V (n + 1))
    (v : V)
    (hres : residualCoord n ∉ active R v) :
    (active R v).card = (retainedActive R v).card := by
  rw [active_eq_cast_retained_of_residual_inactive R v hres]
  simp

/-- Exact saturation with an inactive residual colour is an exact
one-layer projected loss, not merely an upper bound. -/
theorem mem_projectedLoss_of_tight_residual_inactive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (R : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V)
    (htight : exponent v + (active R v).card = n + 1)
    (hres : residualCoord n ∉ active R v) :
    v ∈ projectedLossVertices R exponent := by
  have hcard := active_card_eq_retained_of_residual_inactive R v hres
  have hretN : (retainedActive R v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive R v)
  rw [mem_projectedLossVertices]
  dsimp [projectedFree]
  omega

/-- The exact dyadic profile loss at such a centre is one full
retained completion cube; its pointwise surplus is zero. -/
theorem tight_residual_inactive_exact_dyadic_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (R : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V)
    (htight : exponent v + (active R v).card = n + 1)
    (hres : residualCoord n ∉ active R v) :
    dyadicProfileLoss exponent (projectedFree R) v =
        2 ^ (projectedFree R v) ∧
      dyadicProfileSurplus exponent (projectedFree R) v = 0 := by
  have hmem :=
    mem_projectedLoss_of_tight_residual_inactive
      R exponent v htight hres
  have hexact :=
    (mem_projectedLossVertices R exponent v).1 hmem
  unfold dyadicProfileLoss dyadicProfileSurplus
  rw [hexact, pow_succ]
  have hpos : 0 < 2 ^ (projectedFree R v) := by positivity
  constructor <;> omega

end OrderedEdgeColoring

namespace DirectionData
namespace LocalDirectionCycle

open OrderedEdgeColoring

/-- Actual direction-cycle saturation and inactive top band are
sufficient to certify exact projected loss for the family of
centre exponents. -/
theorem mem_projectedLoss_of_local_tight_residual_inactive
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ j : V, LocalDirectionCycle D j)
    (i : V)
    (htight :
      (cycles i).exponent +
        (D.incidentBands (n + 1) i).card = n + 1)
    (hres : residualCoord n ∉
      active (standardResidualColoring D n
        (by exact_mod_cast ht)) i) :
    i ∈ projectedLossVertices
      (standardResidualColoring D n
        (by exact_mod_cast ht))
      (fun j => (cycles j).exponent) := by
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  have hactive :
      (active B i).card = (D.incidentBands (n + 1) i).card := by
    rw [standardResidual_active_eq_incidentBands_succ]
  have htight' :
      (cycles i).exponent + (active B i).card = n + 1 := by
    rw [hactive]
    exact htight
  exact mem_projectedLoss_of_tight_residual_inactive
    B (fun j => (cycles j).exponent) i htight' hres

#print axioms LocalDirectionCycle.mem_projectedLoss_of_local_tight_residual_inactive

end LocalDirectionCycle
end DirectionData

#print axioms OrderedEdgeColoring.active_eq_cast_retained_of_residual_inactive
#print axioms OrderedEdgeColoring.mem_projectedLoss_of_tight_residual_inactive
#print axioms OrderedEdgeColoring.tight_residual_inactive_exact_dyadic_loss

end JSP000404Research
