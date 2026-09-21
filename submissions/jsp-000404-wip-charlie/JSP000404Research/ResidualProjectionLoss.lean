import JSP000404Research.OneLayerProfileLoss
import JSP000404Research.ResidualActiveDrop
import Mathlib.Tactic

/-!
# Exact one-layer losses in residual projection are residual-inactive

Start with an (n+1)-colour OrderedEdgeColoring and project away the last
(residual) colour.  Let

  nu(v) = n - card(retainedActive(v))

be the free-coordinate count after projection.

Assume the one-exception local bound

  card(active(v)) <= n - exponent(v) + 1.

Then exponent(v) <= nu(v)+1 because retained colours are a subset of all old
active colours.

More importantly, an exact one-layer profile loss

  exponent(v)=r+1,  nu(v)=r

is rigid.  The retained palette has exactly n-r colours, the whole old active
palette also has at most n-r colours, and therefore the residual colour cannot
be active at v.  Equivalently the retained palette is exactly one colour over
the Sendov deficit.

Thus the threshold losses isolated by OneLayerProfileLoss are not residual
edges.  They are precisely residual-inactive vertices at which the retained
palette realizes the unique one-unit phase loss.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def projectedFree
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : ℕ :=
  n - (retainedActive C v).card

theorem retainedActive_card_le_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    (retainedActive C v).card ≤ (active C v).card := by
  classical
  let R : Finset (Fin (n + 1)) :=
    (retainedActive C v).map Fin.castSuccEmb
  have hRsub : R ⊆ active C v := by
    intro c hc
    rcases Finset.mem_map.mp hc with ⟨d, hd, rfl⟩
    exact (castSucc_mem_active_iff_mem_retainedActive C v d).2 hd
  have hc := Finset.card_le_card hRsub
  simpa [R] using hc

/-- The one-exception active bound becomes a one-layer free-profile loss after
dropping the residual coordinate. -/
theorem exponent_le_projectedFree_add_one
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1) :
    ∀ v, exponent v ≤ projectedFree C v + 1 := by
  intro v
  have hret := retainedActive_card_le_active C v
  have hretN : (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  unfold projectedFree
  have hk := hexp v
  have h := honeLoss v
  omega

/-- Exact profile loss forces residual inactivity and exact one-over-deficit
retained saturation. -/
theorem exact_projected_loss_rigidity
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V} {r : ℕ}
    (hk : exponent v = r + 1)
    (hnu : projectedFree C v = r) :
    residualCoord n ∉ active C v ∧
      (retainedActive C v).card =
        n - exponent v + 1 := by
  have hretN : (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  have hrn : r < n := by
    have := hexp v
    rw [hk] at this
    omega
  have hretEq :
      (retainedActive C v).card = n - r := by
    unfold projectedFree at hnu
    omega
  have hactiveLe :
      (active C v).card ≤ n - r := by
    have h := honeLoss v
    rw [hk] at h
    omega
  have hnoRes : residualCoord n ∉ active C v := by
    intro hres
    have hdrop :=
      retainedActive_card_add_one_le_active_of_residual_mem
        C v hres
    rw [hretEq] at hdrop
    omega
  constructor
  · exact hnoRes
  · rw [hretEq, hk]
    omega

/-- Hence every member of the exact threshold-loss set is residual-inactive. -/
theorem residual_inactive_of_mem_layerLoss_projected
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {r : ℕ} {v : V}
    (hv :
      v ∈ layerLossSet exponent (projectedFree C) r) :
    residualCoord n ∉ active C v := by
  have hone :=
    exponent_le_projectedFree_add_one
      C exponent hexp honeLoss
  have hexact :=
    (mem_layerLossSet_iff_exact_one_loss
      exponent (projectedFree C) hone r v).1 hv
  exact (exact_projected_loss_rigidity
    C exponent hexp honeLoss hexact.1 hexact.2).1

#print axioms exponent_le_projectedFree_add_one
#print axioms exact_projected_loss_rigidity
#print axioms residual_inactive_of_mem_layerLoss_projected

end OrderedEdgeColoring
end JSP000404Research
