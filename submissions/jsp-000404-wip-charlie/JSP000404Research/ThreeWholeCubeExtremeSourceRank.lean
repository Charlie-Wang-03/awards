import JSP000404Research.ThreeWholeCubeSourceBitOrder
import JSP000404Research.ThreeWholeCubeGlobalExtreme
import Mathlib.Tactic

/-!
# Source rank in a three-whole-cube star with a global-extreme partner

Let v be the source and s1,s2,s3 its three whole-cube partners.

If one partner si is the global minimum, then its retained code is all false.
Since si differs from v only at ci, the source code has ci=true and the other
two source bits false.  Therefore

  si < v < sj, sk.

Thus the source is immediately above the minimum within the four-vertex star.
Dually, if a partner is the global maximum, the source is immediately below it.

If the source itself is the global extreme, it is of course the first/last
star vertex.  Hence in a unique-support-one terminal whose support-one point is
the unique global extreme, the source can only occupy one of the two ranks
adjacent to that extreme.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem source_between_min_partner_and_other_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v s₁ s₂ s₃ : V}
    (hvs1 : v ≠ s₁)
    (hvs2 : v ≠ s₂)
    (hvs3 : v ≠ s₃)
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc13 : c₁ ≠ c₃)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hs1Loss : s₁ ∈ projectedLossVertices C exponent)
    (hc1V : c₁ ∈ retainedActive C v)
    (hc2V : c₂ ∈ retainedActive C v)
    (hc3V : c₃ ∈ retainedActive C v)
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃)
    (hmin : ∀ w : V, w ≠ s₁ → s₁ < w) :
    s₁ < v ∧ v < s₂ ∧ v < s₃ := by
  have hs1False :
      AllRetainedBitsFalse C s₁ :=
    projectedLoss_global_min_allFalse
      C exponent hs1Loss hmin

  have hstar :=
    threeWholeCubePartners_retainedCode_star
      C hc1V hc2V hc3V h₁ h₂ h₃

  have hc1S1 : c₁ ∈ retainedActive C s₁ := by
    rw [hstar.1.1]
    exact hc1V
  have hc2S1 : c₂ ∈ retainedActive C s₁ := by
    rw [hstar.1.1]
    exact hc2V
  have hc3S1 : c₃ ∈ retainedActive C s₁ := by
    rw [hstar.1.1]
    exact hc3V

  have hS1c1 : retainedBit C s₁ c₁ = false :=
    hs1False c₁ hc1S1
  have hS1c2 : retainedBit C s₁ c₂ = false :=
    hs1False c₂ hc2S1
  have hS1c3 : retainedBit C s₁ c₃ = false :=
    hs1False c₃ hc3S1

  have hvC1 : retainedBit C v c₁ = true := by
    have hf := hstar.1.2.1
    rw [hS1c1] at hf
    cases h : retainedBit C v c₁ <;> simp_all
  have hvC2 : retainedBit C v c₂ = false := by
    have hEq := hstar.1.2.2 c₂ hc2V hc12.symm
    exact hEq.symm.trans hS1c2
  have hvC3 : retainedBit C v c₃ = false := by
    have hEq := hstar.1.2.2 c₃ hc3V hc13.symm
    exact hEq.symm.trans hS1c3

  have hs1v :
      s₁ < v :=
    (wholeCube_partner_lt_source_iff_bit_true
      C exponent hexp honeLoss hvs1.symm
      hvLoss hc1V h₁).2 hvC1
  have hvs2' :
      v < s₂ :=
    (source_lt_wholeCube_partner_iff_bit_false
      C exponent hexp honeLoss hvs2.symm
      hvLoss hc2V h₂).2 hvC2
  have hvs3' :
      v < s₃ :=
    (source_lt_wholeCube_partner_iff_bit_false
      C exponent hexp honeLoss hvs3.symm
      hvLoss hc3V h₃).2 hvC3
  exact ⟨hs1v,hvs2',hvs3'⟩

theorem source_between_other_two_and_max_partner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v s₁ s₂ s₃ : V}
    (hvs1 : v ≠ s₁)
    (hvs2 : v ≠ s₂)
    (hvs3 : v ≠ s₃)
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc13 : c₁ ≠ c₃)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hs1Loss : s₁ ∈ projectedLossVertices C exponent)
    (hc1V : c₁ ∈ retainedActive C v)
    (hc2V : c₂ ∈ retainedActive C v)
    (hc3V : c₃ ∈ retainedActive C v)
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃)
    (hmax : ∀ w : V, w ≠ s₁ → w < s₁) :
    v < s₁ ∧ s₂ < v ∧ s₃ < v := by
  have hs1True :
      AllRetainedBitsTrue C s₁ :=
    projectedLoss_global_max_allTrue
      C exponent hs1Loss hmax

  have hstar :=
    threeWholeCubePartners_retainedCode_star
      C hc1V hc2V hc3V h₁ h₂ h₃

  have hc1S1 : c₁ ∈ retainedActive C s₁ := by
    rw [hstar.1.1]
    exact hc1V
  have hc2S1 : c₂ ∈ retainedActive C s₁ := by
    rw [hstar.1.1]
    exact hc2V
  have hc3S1 : c₃ ∈ retainedActive C s₁ := by
    rw [hstar.1.1]
    exact hc3V

  have hS1c1 : retainedBit C s₁ c₁ = true :=
    hs1True c₁ hc1S1
  have hS1c2 : retainedBit C s₁ c₂ = true :=
    hs1True c₂ hc2S1
  have hS1c3 : retainedBit C s₁ c₃ = true :=
    hs1True c₃ hc3S1

  have hvC1 : retainedBit C v c₁ = false := by
    have hf := hstar.1.2.1
    rw [hS1c1] at hf
    cases h : retainedBit C v c₁ <;> simp_all
  have hvC2 : retainedBit C v c₂ = true := by
    have hEq := hstar.1.2.2 c₂ hc2V hc12.symm
    exact hEq.symm.trans hS1c2
  have hvC3 : retainedBit C v c₃ = true := by
    have hEq := hstar.1.2.2 c₃ hc3V hc13.symm
    exact hEq.symm.trans hS1c3

  have hvs1' :
      v < s₁ :=
    (source_lt_wholeCube_partner_iff_bit_false
      C exponent hexp honeLoss hvs1.symm
      hvLoss hc1V h₁).2 hvC1
  have hs2v :
      s₂ < v :=
    (wholeCube_partner_lt_source_iff_bit_true
      C exponent hexp honeLoss hvs2.symm
      hvLoss hc2V h₂).2 hvC2
  have hs3v :
      s₃ < v :=
    (wholeCube_partner_lt_source_iff_bit_true
      C exponent hexp honeLoss hvs3.symm
      hvLoss hc3V h₃).2 hvC3
  exact ⟨hvs1',hs2v,hs3v⟩

#print axioms source_between_min_partner_and_other_two
#print axioms source_between_other_two_and_max_partner

end OrderedEdgeColoring
end JSP000404Research
