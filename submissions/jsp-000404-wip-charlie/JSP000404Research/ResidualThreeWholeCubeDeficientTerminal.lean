import JSP000404Research.ResidualThreeWholeCubeSevenCover
import JSP000404Research.ResidualWholeCubePairExtraSharedWitness
import Mathlib.Tactic

/-!
# Three whole-cube partners form a four-vertex deficient obstruction

If a second-layer projected-loss vertex v has a whole-cube partner at each of
its three active coordinates, and all three partners are themselves
second-layer projected-loss vertices, then the four enlarged candidate blocks
are contained in the seven-cube cover.

Each base completion cube has cardinality 2^(n-3), so the union has size at
most 7*2^(n-3).  The four dyadic demands sum to

  4*2^(n-2) = 8*2^(n-3),

hence the four-vertex family is strictly BlockDeficient.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem threeWholeCubePartners_four_vertex_blockDeficient
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {v s₁ s₂ s₃ : V}
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc13 : c₁ ≠ c₃)
    (hc23 : c₂ ≠ c₃)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hs1Loss : s₁ ∈ projectedLossVertices C exponent)
    (hs2Loss : s₂ ∈ projectedLossVertices C exponent)
    (hs3Loss : s₃ ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hs1Second : exponent s₁ = n - 2)
    (hs2Second : exponent s₂ = n - 2)
    (hs3Second : exponent s₃ = n - 2)
    (hactive :
      retainedActive C v = {c₁,c₂,c₃})
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃) :
    BlockDeficient
      (fun q => 2 ^ exponent q)
      (enlargedProjectedCandidateBlock C exponent)
      ({v,s₁,s₂,s₃} : Finset V) := by
  classical

  have hc1V : c₁ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc2V : c₂ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc3V : c₃ ∈ retainedActive C v := by
    rw [hactive]
    simp

  have hs1v : s₁ ≠ v :=
    wholeCubeQTPair_ne_of_active C hc1V h₁
  have hs2v : s₂ ≠ v :=
    wholeCubeQTPair_ne_of_active C hc2V h₂
  have hs3v : s₃ ≠ v :=
    wholeCubeQTPair_ne_of_active C hc3V h₃
  have hs12 : s₁ ≠ s₂ :=
    wholeCubeQTPair_partners_ne_of_coordinates_ne
      C hc1V hc2V hc12 h₁ h₂
  have hs13 : s₁ ≠ s₃ :=
    wholeCubeQTPair_partners_ne_of_coordinates_ne
      C hc1V hc3V hc13 h₁ h₃
  have hs23 : s₂ ≠ s₃ :=
    wholeCubeQTPair_partners_ne_of_coordinates_ne
      C hc2V hc3V hc23 h₂ h₃

  let U : Finset V := {v,s₁,s₂,s₃}
  let S := sevenCubeUnion C v c₁ c₂ c₃

  have hvSub :
      enlargedProjectedCandidateBlock C exponent v ⊆ S := by
    rw [enlargedProjectedCandidateBlock_loss
      C exponent hvLoss]
    exact source_allActiveBlock_subset_sevenCubeUnion
      C hactive

  have hs1Sub :
      enlargedProjectedCandidateBlock C exponent s₁ ⊆ S := by
    rw [enlargedProjectedCandidateBlock_loss
      C exponent hs1Loss]
    exact partner_allActiveBlock_subset_sevenCubeUnion_first
      C hc12 hc13 hactive h₁

  have hs2Sub :
      enlargedProjectedCandidateBlock C exponent s₂ ⊆ S := by
    rw [enlargedProjectedCandidateBlock_loss
      C exponent hs2Loss]
    exact partner_allActiveBlock_subset_sevenCubeUnion_second
      C hc12 hc23 hactive h₂

  have hs3Sub :
      enlargedProjectedCandidateBlock C exponent s₃ ⊆ S := by
    rw [enlargedProjectedCandidateBlock_loss
      C exponent hs3Loss]
    exact partner_allActiveBlock_subset_sevenCubeUnion_third
      C hc13 hc23 hactive h₃

  have hUnionSub :
      U.biUnion
        (enlargedProjectedCandidateBlock C exponent) ⊆ S := by
    intro word hword
    obtain ⟨q,hqU,hqWord⟩ :=
      Finset.mem_biUnion.mp hword
    dsimp [U] at hqU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqU
    rcases hqU with rfl | rfl | rfl | rfl
    · exact hvSub hqWord
    · exact hs1Sub hqWord
    · exact hs2Sub hqWord
    · exact hs3Sub hqWord

  have hUnionCard :
      (U.biUnion
        (enlargedProjectedCandidateBlock C exponent)).card
        ≤ 7 * (retainedCompletionWords C v).card := by
    exact (Finset.card_le_card hUnionSub).trans
      (sevenCubeUnion_card_le C v c₁ c₂ c₃)

  have hQcard :
      (retainedCompletionWords C v).card =
        2 ^ (n - 3) :=
    secondLayer_projectedLoss_completion_card_eq
      C exponent hn3 hvLoss hvSecond

  have hUnionCard' :
      (U.biUnion
        (enlargedProjectedCandidateBlock C exponent)).card
        ≤ 7 * 2 ^ (n - 3) := by
    simpa [hQcard] using hUnionCard

  have hDemand :
      (∑ q ∈ U, 2 ^ exponent q) =
        4 * 2 ^ (n - 2) := by
    dsimp [U]
    simp [hvSecond,hs1Second,hs2Second,hs3Second,
      hs1v,hs2v,hs3v,hs12,hs13,hs23,
      Ne.symm hs1v,Ne.symm hs2v,Ne.symm hs3v,
      Ne.symm hs12,Ne.symm hs13,Ne.symm hs23]
    ring

  have hpow :
      4 * 2 ^ (n - 2) =
        8 * 2 ^ (n - 3) := by
    have hs : n - 3 + 1 = n - 2 := by omega
    rw [← hs,pow_succ]
    ring

  have hbasePos : 0 < 2 ^ (n - 3) :=
    Nat.two_pow_pos _

  unfold BlockDeficient
  change
    (U.biUnion
      (enlargedProjectedCandidateBlock C exponent)).card
      <
    ∑ q ∈ U, 2 ^ exponent q
  rw [hDemand,hpow]
  omega

#print axioms threeWholeCubePartners_four_vertex_blockDeficient

end OrderedEdgeColoring
end JSP000404Research
