import JSP000404Research.ResidualThreeWholeCubeMinimalCoreCollapse
import JSP000404Research.ResidualWholeCubeOffOwnerExit
import Mathlib.Tactic

/-!
# Exact-four off-owner exit matrix for a three-whole-cube minimal core

If a saturated three-whole-cube star lies in an inclusion-minimal deficient
core, the core is exactly the four star vertices.  The general off-owner exit
from any translated partner therefore has nowhere else to go:

* its displaced coordinate is one of the other two owner coordinates;
* its third source is one of the other two partners.

This turns the augmenting exit into a finite 2 x 2 provenance matrix.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def ExactFourOffOwnerExitAt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (partner other₁ other₂ : V)
    (alt₁ alt₂ : Fin n) : Prop :=
  ∃ word : Fin n → Bool,
  ∃ d : Fin n,
  ∃ w : V,
    (d = alt₁ ∨ d = alt₂) ∧
    (w = other₁ ∨ w = other₂) ∧
    d ∈ retainedActive C partner ∧
    word ∈ translatedCompletionWords C partner d ∧
    word ∈ enlargedProjectedCandidateBlock C exponent w

theorem threeWholeCube_exactFour_offOwner_exit_first
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock C exponent)
        T)
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
    (hactive : retainedActive C v = {c₁,c₂,c₃})
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃) :
    ExactFourOffOwnerExitAt C exponent v s₂ s₃ c₂ c₃ := by
  have hc1V : c₁ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hs1v : s₁ ≠ v :=
    wholeCubeQTPair_ne_of_active C hc1V h₁
  have hT :
      T = ({v,s₁,s₂,s₃} : Finset V) :=
    threeWholeCubePartners_minimal_core_eq_four
      C exponent hn3 hmin
      hvT hs1T hs2T hs3T
      hc12 hc13 hc23
      hvLoss hs1Loss hs2Loss hs3Loss
      hvSecond hs1Second hs2Second hs3Second
      hactive h₁ h₂ h₃
  obtain ⟨word,d,w,hdActive,hdc,hdWord,hwBlock,
      _hnot1,_hnotV,hwT,hwNe1,hwNeV⟩ :=
    minimal_core_wholeCubeQTPair_has_off_owner_third_exit
      C exponent hn3 hdef hmin
      hvT hs1v hs1Loss hvLoss hvSecond
      hc1V h₁
  have hdV : d ∈ retainedActive C v := by
    rw [← h₁.1]
    exact hdActive
  have hdSet : d ∈ ({c₁,c₂,c₃} : Finset (Fin n)) := by
    rw [← hactive]
    exact hdV
  have hdAlt : d = c₂ ∨ d = c₃ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdSet
    rcases hdSet with h | h | h
    · exact False.elim (hdc h)
    · exact Or.inl h
    · exact Or.inr h
  have hwSet : w ∈ ({v,s₁,s₂,s₃} : Finset V) := by
    rw [← hT]
    exact hwT
  have hwAlt : w = s₂ ∨ w = s₃ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwSet
    rcases hwSet with h | h | h | h
    · exact False.elim (hwNeV h)
    · exact False.elim (hwNe1 h)
    · exact Or.inl h
    · exact Or.inr h
  exact ⟨word,d,w,hdAlt,hwAlt,hdActive,hdWord,hwBlock⟩

#print axioms threeWholeCube_exactFour_offOwner_exit_first

theorem threeWholeCube_exactFour_offOwner_exit_second
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock C exponent)
        T)
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
    (hactive : retainedActive C v = {c₁,c₂,c₃})
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃) :
    ExactFourOffOwnerExitAt C exponent v s₁ s₃ c₁ c₃ := by
  have hactive' :
      retainedActive C v = {c₂,c₁,c₃} := by
    rw [hactive]
    ext q
    simp [or_assoc, or_left_comm, or_comm]
  exact threeWholeCube_exactFour_offOwner_exit_first
    C exponent hn3 hdef hmin
    hvT hs2T hs1T hs3T
    hc12.symm hc23 hc13
    hvLoss hs2Loss hs1Loss hs3Loss
    hvSecond hs2Second hs1Second hs3Second
    hactive' h₂ h₁ h₃

theorem threeWholeCube_exactFour_offOwner_exit_third
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock C exponent)
        T)
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
    (hactive : retainedActive C v = {c₁,c₂,c₃})
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃) :
    ExactFourOffOwnerExitAt C exponent v s₁ s₂ c₁ c₂ := by
  have hactive' :
      retainedActive C v = {c₃,c₁,c₂} := by
    rw [hactive]
    ext q
    simp [or_assoc, or_left_comm, or_comm]
  exact threeWholeCube_exactFour_offOwner_exit_first
    C exponent hn3 hdef hmin
    hvT hs3T hs1T hs2T
    hc13.symm hc23.symm hc12
    hvLoss hs3Loss hs1Loss hs2Loss
    hvSecond hs3Second hs1Second hs2Second
    hactive' h₃ h₁ h₂

theorem threeWholeCube_exactFour_offOwner_exit_matrix
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock C exponent)
        T)
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
    (hactive : retainedActive C v = {c₁,c₂,c₃})
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃) :
    ExactFourOffOwnerExitAt C exponent v s₂ s₃ c₂ c₃ ∧
    ExactFourOffOwnerExitAt C exponent v s₁ s₃ c₁ c₃ ∧
    ExactFourOffOwnerExitAt C exponent v s₁ s₂ c₁ c₂ := by
  constructor
  · exact threeWholeCube_exactFour_offOwner_exit_first
      C exponent hn3 hdef hmin
      hvT hs1T hs2T hs3T
      hc12 hc13 hc23
      hvLoss hs1Loss hs2Loss hs3Loss
      hvSecond hs1Second hs2Second hs3Second
      hactive h₁ h₂ h₃
  · constructor
    · exact threeWholeCube_exactFour_offOwner_exit_second
        C exponent hn3 hdef hmin
        hvT hs1T hs2T hs3T
        hc12 hc13 hc23
        hvLoss hs1Loss hs2Loss hs3Loss
        hvSecond hs1Second hs2Second hs3Second
        hactive h₁ h₂ h₃
    · exact threeWholeCube_exactFour_offOwner_exit_third
        C exponent hn3 hdef hmin
        hvT hs1T hs2T hs3T
        hc12 hc13 hc23
        hvLoss hs1Loss hs2Loss hs3Loss
        hvSecond hs1Second hs2Second hs3Second
        hactive h₁ h₂ h₃

#print axioms threeWholeCube_exactFour_offOwner_exit_second
#print axioms threeWholeCube_exactFour_offOwner_exit_third
#print axioms threeWholeCube_exactFour_offOwner_exit_matrix

end OrderedEdgeColoring
end JSP000404Research
