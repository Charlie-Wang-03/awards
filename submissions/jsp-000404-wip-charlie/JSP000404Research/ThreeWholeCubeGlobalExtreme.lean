import JSP000404Research.ThreeWholeCubeRetainedCodeStar
import JSP000404Research.ResidualProjectedLossCore
import Mathlib.Tactic

/-!
# Extreme vertex forced by a saturated whole-cube retained-code star

For a projected-loss vertex the residual colour is inactive, so every incident
edge is retained.  If every retained-active coordinate has retained bit false,
every incident edge is outgoing and the vertex is the global minimum of the
ambient linear order.  Dually, an all-true retained code gives the global
maximum.

For a three-whole-cube star, the source code and its three one-bit flips form
four vertices of the Boolean 3-cube.  Among those four profiles one is always
constant: either 000 or 111.  Hence one of the four saturated vertices is a
global order extreme.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def AllRetainedBitsFalse
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Prop :=
  ∀ c : Fin n,
    c ∈ retainedActive C v →
    retainedBit C v c = false

def AllRetainedBitsTrue
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Prop :=
  ∀ c : Fin n,
    c ∈ retainedActive C v →
    retainedBit C v c = true

theorem projectedLoss_allFalse_is_global_min
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hfalse : AllRetainedBitsFalse C v) :
    ∀ w : V, w ≠ v → v < w := by
  intro w hwv
  rcases lt_or_gt_of_ne hwv with hwvlt | hvwlt
  · have hret : (C.color w v).val < n := by
      by_contra hnot
      have hres : IsResidual C w v := hnot
      have hactive :=
        (residualCoord_mem_active_of_isResidual C hwvlt hres).2
      exact
        (residual_inactive_of_mem_projectedLossVertices
          C exponent hexp honeLoss hvLoss) hactive
    let e : Fin n := retainedColor C w v hret
    have hcast : e.castSucc = C.color w v := by
      apply Fin.ext
      rfl
    have heV : e ∈ retainedActive C v := by
      classical
      simp only [retainedActive, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact Or.inl ⟨w, hwvlt, hcast.symm⟩
    have htrue : retainedBit C v e = true := by
      unfold retainedBit
      rw [hcast]
      exact edgeColor_bit_upper_eq_true C hwvlt
    have hzero := hfalse e heV
    rw [hzero] at htrue
    simp at htrue
  · exact hvwlt

theorem projectedLoss_allTrue_is_global_max
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (htrue : AllRetainedBitsTrue C v) :
    ∀ w : V, w ≠ v → w < v := by
  intro w hwv
  rcases lt_or_gt_of_ne hwv with hwvlt | hvwlt
  · exact hwvlt
  · have hret : (C.color v w).val < n := by
      by_contra hnot
      have hres : IsResidual C v w := hnot
      have hactive :=
        (residualCoord_mem_active_of_isResidual C hvwlt hres).1
      exact
        (residual_inactive_of_mem_projectedLossVertices
          C exponent hexp honeLoss hvLoss) hactive
    let e : Fin n := retainedColor C v w hret
    have hcast : e.castSucc = C.color v w := by
      apply Fin.ext
      rfl
    have heV : e ∈ retainedActive C v := by
      classical
      simp only [retainedActive, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact Or.inr ⟨w, hvwlt, hcast.symm⟩
    have hfalse : retainedBit C v e = false := by
      unfold retainedBit
      rw [hcast]
      exact edgeColor_bit_lower_eq_false C hvwlt
    have hone := htrue e heV
    rw [hone] at hfalse
    simp at hfalse

theorem bool_three_star_has_constant_profile
    (b₁ b₂ b₃ : Bool) :
    (b₁ = false ∧ b₂ = false ∧ b₃ = false)
    ∨ (b₁ = true ∧ b₂ = true ∧ b₃ = true)
    ∨ ((!b₁) = false ∧ b₂ = false ∧ b₃ = false)
    ∨ ((!b₁) = true ∧ b₂ = true ∧ b₃ = true)
    ∨ (b₁ = false ∧ (!b₂) = false ∧ b₃ = false)
    ∨ (b₁ = true ∧ (!b₂) = true ∧ b₃ = true)
    ∨ (b₁ = false ∧ b₂ = false ∧ (!b₃) = false)
    ∨ (b₁ = true ∧ b₂ = true ∧ (!b₃) = true) := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> simp

theorem threeWholeCubePartners_has_global_extreme
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v s₁ s₂ s₃ : V}
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc13 : c₁ ≠ c₃)
    (hc23 : c₂ ≠ c₃)
    (hactive :
      retainedActive C v = {c₁,c₂,c₃})
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hs1Loss : s₁ ∈ projectedLossVertices C exponent)
    (hs2Loss : s₂ ∈ projectedLossVertices C exponent)
    (hs3Loss : s₃ ∈ projectedLossVertices C exponent)
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃) :
    (
      (∀ w : V, w ≠ v → v < w) ∨
      (∀ w : V, w ≠ v → w < v)
    )
    ∨
    (
      (∀ w : V, w ≠ s₁ → s₁ < w) ∨
      (∀ w : V, w ≠ s₁ → w < s₁)
    )
    ∨
    (
      (∀ w : V, w ≠ s₂ → s₂ < w) ∨
      (∀ w : V, w ≠ s₂ → w < s₂)
    )
    ∨
    (
      (∀ w : V, w ≠ s₃ → s₃ < w) ∨
      (∀ w : V, w ≠ s₃ → w < s₃)
    ) := by
  have hc1V : c₁ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc2V : c₂ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc3V : c₃ ∈ retainedActive C v := by
    rw [hactive]
    simp

  have hstar :=
    threeWholeCubePartners_retainedCode_star
      C hc1V hc2V hc3V h₁ h₂ h₃

  let b₁ := retainedBit C v c₁
  let b₂ := retainedBit C v c₂
  let b₃ := retainedBit C v c₃
  have hconst :=
    bool_three_star_has_constant_profile b₁ b₂ b₃

  have baseFalse
      (hbits : b₁ = false ∧ b₂ = false ∧ b₃ = false) :
      AllRetainedBitsFalse C v := by
    intro c hc
    rw [hactive] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact hbits.1
    · exact hbits.2.1
    · exact hbits.2.2

  have baseTrue
      (hbits : b₁ = true ∧ b₂ = true ∧ b₃ = true) :
      AllRetainedBitsTrue C v := by
    intro c hc
    rw [hactive] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact hbits.1
    · exact hbits.2.1
    · exact hbits.2.2

  have partner1False
      (hbits : (!b₁) = false ∧ b₂ = false ∧ b₃ = false) :
      AllRetainedBitsFalse C s₁ := by
    intro c hc
    have hcV : c ∈ retainedActive C v := by
      rw [← hstar.1.1]
      exact hc
    rw [hactive] at hcV
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcV
    rcases hcV with rfl | rfl | rfl
    · simpa [b₁] using hstar.1.2.1.trans hbits.1
    · exact (hstar.1.2.2 c₂ hc2V hc12.symm).trans hbits.2.1
    · exact (hstar.1.2.2 c₃ hc3V hc13.symm).trans hbits.2.2

  have partner1True
      (hbits : (!b₁) = true ∧ b₂ = true ∧ b₃ = true) :
      AllRetainedBitsTrue C s₁ := by
    intro c hc
    have hcV : c ∈ retainedActive C v := by
      rw [← hstar.1.1]
      exact hc
    rw [hactive] at hcV
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcV
    rcases hcV with rfl | rfl | rfl
    · simpa [b₁] using hstar.1.2.1.trans hbits.1
    · exact (hstar.1.2.2 c₂ hc2V hc12.symm).trans hbits.2.1
    · exact (hstar.1.2.2 c₃ hc3V hc13.symm).trans hbits.2.2

  have partner2False
      (hbits : b₁ = false ∧ (!b₂) = false ∧ b₃ = false) :
      AllRetainedBitsFalse C s₂ := by
    intro c hc
    have hcV : c ∈ retainedActive C v := by
      rw [← hstar.2.1.1]
      exact hc
    rw [hactive] at hcV
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcV
    rcases hcV with rfl | rfl | rfl
    · exact (hstar.2.1.2.2 c₁ hc1V hc12).trans hbits.1
    · simpa [b₂] using hstar.2.1.2.1.trans hbits.2.1
    · exact (hstar.2.1.2.2 c₃ hc3V hc23.symm).trans hbits.2.2

  have partner2True
      (hbits : b₁ = true ∧ (!b₂) = true ∧ b₃ = true) :
      AllRetainedBitsTrue C s₂ := by
    intro c hc
    have hcV : c ∈ retainedActive C v := by
      rw [← hstar.2.1.1]
      exact hc
    rw [hactive] at hcV
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcV
    rcases hcV with rfl | rfl | rfl
    · exact (hstar.2.1.2.2 c₁ hc1V hc12).trans hbits.1
    · simpa [b₂] using hstar.2.1.2.1.trans hbits.2.1
    · exact (hstar.2.1.2.2 c₃ hc3V hc23.symm).trans hbits.2.2

  have partner3False
      (hbits : b₁ = false ∧ b₂ = false ∧ (!b₃) = false) :
      AllRetainedBitsFalse C s₃ := by
    intro c hc
    have hcV : c ∈ retainedActive C v := by
      rw [← hstar.2.2.1]
      exact hc
    rw [hactive] at hcV
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcV
    rcases hcV with rfl | rfl | rfl
    · exact (hstar.2.2.2.2 c₁ hc1V hc13).trans hbits.1
    · exact (hstar.2.2.2.2 c₂ hc2V hc23).trans hbits.2.1
    · simpa [b₃] using hstar.2.2.2.1.trans hbits.2.2

  have partner3True
      (hbits : b₁ = true ∧ b₂ = true ∧ (!b₃) = true) :
      AllRetainedBitsTrue C s₃ := by
    intro c hc
    have hcV : c ∈ retainedActive C v := by
      rw [← hstar.2.2.1]
      exact hc
    rw [hactive] at hcV
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcV
    rcases hcV with rfl | rfl | rfl
    · exact (hstar.2.2.2.2 c₁ hc1V hc13).trans hbits.1
    · exact (hstar.2.2.2.2 c₂ hc2V hc23).trans hbits.2.1
    · simpa [b₃] using hstar.2.2.2.1.trans hbits.2.2

  rcases hconst with h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl
      (projectedLoss_allFalse_is_global_min
        C exponent hexp honeLoss hvLoss (baseFalse h)))
  · exact Or.inl (Or.inr
      (projectedLoss_allTrue_is_global_max
        C exponent hexp honeLoss hvLoss (baseTrue h)))
  · exact Or.inr (Or.inl (Or.inl
      (projectedLoss_allFalse_is_global_min
        C exponent hexp honeLoss hs1Loss (partner1False h))))
  · exact Or.inr (Or.inl (Or.inr
      (projectedLoss_allTrue_is_global_max
        C exponent hexp honeLoss hs1Loss (partner1True h))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl
      (projectedLoss_allFalse_is_global_min
        C exponent hexp honeLoss hs2Loss (partner2False h)))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr
      (projectedLoss_allTrue_is_global_max
        C exponent hexp honeLoss hs2Loss (partner2True h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (projectedLoss_allFalse_is_global_min
        C exponent hexp honeLoss hs3Loss (partner3False h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (projectedLoss_allTrue_is_global_max
        C exponent hexp honeLoss hs3Loss (partner3True h)))))

#print axioms projectedLoss_allFalse_is_global_min
#print axioms projectedLoss_allTrue_is_global_max
#print axioms threeWholeCubePartners_has_global_extreme

end OrderedEdgeColoring
end JSP000404Research
