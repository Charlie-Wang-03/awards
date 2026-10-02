import JSP000404Research.ResidualWholeCubePartnerUniqueness
import Mathlib.Tactic

/-!
# Three whole-cube partners exhaust all projected-loss rematches

If a source v has active palette {c1,c2,c3} and projected-loss whole-cube
partners s1,s2,s3 at those coordinates, then every further projected-loss
WholeCubeQTPair (w,v,d) with d active is one of exactly those three states.

Thus the lossless rematching graph at a fixed second-layer translated endpoint
has no hidden fourth state: after the three coordinates are populated, every
new projected-loss rematch is a repetition.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem threeWholeCubePartners_exhaust_projectedLoss_rematches
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v s₁ s₂ s₃ w : V}
    {c₁ c₂ c₃ d : Fin n}
    (hactive :
      retainedActive C v = {c₁,c₂,c₃})
    (hs1Loss : s₁ ∈ projectedLossVertices C exponent)
    (hs2Loss : s₂ ∈ projectedLossVertices C exponent)
    (hs3Loss : s₃ ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃)
    (hdV : d ∈ retainedActive C v)
    (hw : WholeCubeQTPair C w v d) :
    (d = c₁ ∧ w = s₁)
    ∨ (d = c₂ ∧ w = s₂)
    ∨ (d = c₃ ∧ w = s₃) := by
  have hd :
      d = c₁ ∨ d = c₂ ∨ d = c₃ := by
    rw [hactive] at hdV
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hdV
  rcases hd with rfl | rfl | rfl
  · left
    refine ⟨rfl,?_⟩
    exact projectedLoss_wholeCube_partner_unique_at_coordinate
      C exponent hexp honeLoss
      hwLoss hs1Loss hw h₁
  · right; left
    refine ⟨rfl,?_⟩
    exact projectedLoss_wholeCube_partner_unique_at_coordinate
      C exponent hexp honeLoss
      hwLoss hs2Loss hw h₂
  · right; right
    refine ⟨rfl,?_⟩
    exact projectedLoss_wholeCube_partner_unique_at_coordinate
      C exponent hexp honeLoss
      hwLoss hs3Loss hw h₃

#print axioms threeWholeCubePartners_exhaust_projectedLoss_rematches

end OrderedEdgeColoring
end JSP000404Research
