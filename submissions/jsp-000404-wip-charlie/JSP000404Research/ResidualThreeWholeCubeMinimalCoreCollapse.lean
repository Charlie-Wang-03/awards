import JSP000404Research.ResidualThreeWholeCubeDeficientTerminal
import Mathlib.Tactic

/-!
# Minimal-core collapse from a deficient subset

If T is inclusion-minimal among BlockDeficient sets, any deficient subset
U ⊆ T must equal T.

Applied to the saturated three-whole-cube terminal, once the source v and all
three coordinate partners belong to T, the minimal core is exactly those four
vertices.
-/

namespace JSP000404Research

theorem deficient_subset_eq_minimal_core
    {V W : Type*}
    [DecidableEq V]
    (weight : V → ℕ)
    (blocks : V → Finset W)
    {T U : Finset V}
    (hmin :
      ∀ S : Finset V,
        S ⊂ T →
        ¬ BlockDeficient weight blocks S)
    (hUT : U ⊆ T)
    (hUdef : BlockDeficient weight blocks U) :
    U = T := by
  by_contra hne
  have hproper : U ⊂ T :=
    ⟨hUT,hne⟩
  exact hmin U hproper hUdef

namespace OrderedEdgeColoring

theorem threeWholeCubePartners_minimal_core_eq_four
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun q => 2 ^ exponent q)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {v s₁ s₂ s₃ : V}
    {c₁ c₂ c₃ : Fin n}
    (hvT : v ∈ T)
    (hs1T : s₁ ∈ T)
    (hs2T : s₂ ∈ T)
    (hs3T : s₃ ∈ T)
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
    T = ({v,s₁,s₂,s₃} : Finset V) := by
  let U : Finset V := {v,s₁,s₂,s₃}
  have hUT : U ⊆ T := by
    intro q hq
    simp only [U,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hvT
    · exact hs1T
    · exact hs2T
    · exact hs3T
  have hUdef :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock C exponent)
        U := by
    simpa [U] using
      threeWholeCubePartners_four_vertex_blockDeficient
        C exponent hn3
        hc12 hc13 hc23
        hvLoss hs1Loss hs2Loss hs3Loss
        hvSecond hs1Second hs2Second hs3Second
        hactive h₁ h₂ h₃
  have hEq :
      U = T :=
    deficient_subset_eq_minimal_core
      (fun q => 2 ^ exponent q)
      (enlargedProjectedCandidateBlock C exponent)
      hmin hUT hUdef
  exact hEq.symm

#print axioms deficient_subset_eq_minimal_core
#print axioms threeWholeCubePartners_minimal_core_eq_four

end OrderedEdgeColoring
end JSP000404Research
