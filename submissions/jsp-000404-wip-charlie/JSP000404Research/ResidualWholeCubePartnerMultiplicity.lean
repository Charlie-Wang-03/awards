import JSP000404Research.ResidualWholeCubePartnerUniqueness
import JSP000404Research.ResidualWholeCubePairExtraSharedWitness
import Mathlib.Tactic

/-!
# At most three projected-loss whole-cube partners at a second-layer source

A second-layer projected-loss vertex has exactly three retained-active
coordinates.  For each active coordinate there is at most one projected-loss
WholeCubeQTPair partner.  Therefore four pairwise-distinct projected-loss
partners cannot coexist.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem no_four_distinct_projectedLoss_wholeCube_partners_secondLayer
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    (hn3 : 3 ≤ n)
    {v s₁ s₂ s₃ s₄ : V}
    {c₁ c₂ c₃ c₄ : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hs1Loss : s₁ ∈ projectedLossVertices C exponent)
    (hs2Loss : s₂ ∈ projectedLossVertices C exponent)
    (hs3Loss : s₃ ∈ projectedLossVertices C exponent)
    (hs4Loss : s₄ ∈ projectedLossVertices C exponent)
    (hc1 : c₁ ∈ retainedActive C v)
    (hc2 : c₂ ∈ retainedActive C v)
    (hc3 : c₃ ∈ retainedActive C v)
    (hc4 : c₄ ∈ retainedActive C v)
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃)
    (h₄ : WholeCubeQTPair C s₄ v c₄)
    (hs12 : s₁ ≠ s₂)
    (hs13 : s₁ ≠ s₃)
    (hs14 : s₁ ≠ s₄)
    (hs23 : s₂ ≠ s₃)
    (hs24 : s₂ ≠ s₄)
    (hs34 : s₃ ≠ s₄) :
    False := by
  have hc12 : c₁ ≠ c₂ := by
    intro h
    subst c₂
    exact hs12
      (projectedLoss_wholeCube_partner_unique_at_coordinate
        C exponent hexp honeLoss hs1Loss hs2Loss h₁ h₂)
  have hc13 : c₁ ≠ c₃ := by
    intro h
    subst c₃
    exact hs13
      (projectedLoss_wholeCube_partner_unique_at_coordinate
        C exponent hexp honeLoss hs1Loss hs3Loss h₁ h₃)
  have hc14 : c₁ ≠ c₄ := by
    intro h
    subst c₄
    exact hs14
      (projectedLoss_wholeCube_partner_unique_at_coordinate
        C exponent hexp honeLoss hs1Loss hs4Loss h₁ h₄)
  have hc23 : c₂ ≠ c₃ := by
    intro h
    subst c₃
    exact hs23
      (projectedLoss_wholeCube_partner_unique_at_coordinate
        C exponent hexp honeLoss hs2Loss hs3Loss h₂ h₃)
  have hc24 : c₂ ≠ c₄ := by
    intro h
    subst c₄
    exact hs24
      (projectedLoss_wholeCube_partner_unique_at_coordinate
        C exponent hexp honeLoss hs2Loss hs4Loss h₂ h₄)
  have hc34 : c₃ ≠ c₄ := by
    intro h
    subst c₄
    exact hs34
      (projectedLoss_wholeCube_partner_unique_at_coordinate
        C exponent hexp honeLoss hs3Loss hs4Loss h₃ h₄)

  let S : Finset (Fin n) := {c₁,c₂,c₃,c₄}
  have hSsub : S ⊆ retainedActive C v := by
    intro c hc
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact hc1
    · exact hc2
    · exact hc3
    · exact hc4
  have hScard : S.card = 4 := by
    simp [S,hc12,hc13,hc14,hc23,hc24,hc34,
      Ne.symm hc12,Ne.symm hc13,Ne.symm hc14,
      Ne.symm hc23,Ne.symm hc24,Ne.symm hc34]
  have hactiveCard :
      (retainedActive C v).card = 3 :=
    secondLayer_projectedLoss_retainedActive_card_eq_three
      C exponent hn3 hvLoss hvSecond
  have hcardLe := Finset.card_le_card hSsub
  rw [hScard,hactiveCard] at hcardLe
  omega

#print axioms no_four_distinct_projectedLoss_wholeCube_partners_secondLayer

end OrderedEdgeColoring
end JSP000404Research
