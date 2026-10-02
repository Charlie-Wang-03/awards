import JSP000404Research.ThreeWholeCubeRetainedCodeStar
import JSP000404Research.ResidualSecondLayerTripleCanonical
import Mathlib.Tactic

/-!
# Source-bit order partition in a three-whole-cube star

For a whole-cube Q/T pair (s,v,c), choose any completion word of s.  It is a
translated word at v along c.  The Q/T owner-edge semantics says that the
v--s edge has colour c.  Hence:

* v < s iff retainedBit(v,c)=false;
* s < v iff retainedBit(v,c)=true.

Applied to three whole-cube partners, the three source bits partition the
partners exactly into those lying below and above the source.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCube_partner_order_of_source_bit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s v : V} {c : Fin n}
    (hsv : s ≠ v)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    (
      retainedBit C v c = false ∧ v < s
    )
    ∨
    (
      retainedBit C v c = true ∧ s < v
    ) := by
  have hnon :
      (retainedCompletionWords C s).Nonempty := by
    rw [retainedCompletionWords_nonempty_iff]
  obtain ⟨word,hsQ⟩ := hnon
  have hvT :
      word ∈ translatedCompletionWords C v c := by
    rw [hwhole.2]
    exact hsQ
  have hsem :=
    QTT_owner_edge_semantics
      C exponent hexp honeLoss
      hsv hvLoss hcV hsQ hvT
  rcases hsem with hleft | hright
  · obtain ⟨hvs,hret,hcol,hword⟩ := hleft
    right
    refine ⟨?_,hvs⟩
    have hIn :
        c ∈ incomingRetained C v := by
      apply (mem_incomingRetained_iff C v c).2
      refine ⟨s,hvs,?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val hcol
      simpa [retainedColor] using hv
    exact
      (mem_incomingRetained_iff_retainedBit_true C v c).1 hIn
  · obtain ⟨hsvlt,hret,hcol,hword⟩ := hright
    left
    refine ⟨?_,hsvlt⟩
    have hOut :
        c ∈ outgoingRetained C v := by
      apply (mem_outgoingRetained_iff C v c).2
      refine ⟨s,hsvlt,?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val hcol
      simpa [retainedColor] using hv
    exact retainedBit_false_of_outgoingRetained C hOut

theorem wholeCube_partner_lt_source_iff_bit_true
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s v : V} {c : Fin n}
    (hsv : s ≠ v)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    s < v ↔ retainedBit C v c = true := by
  have h :=
    wholeCube_partner_order_of_source_bit
      C exponent hexp honeLoss hsv hvLoss hcV hwhole
  constructor
  · intro hsvlt
    rcases h with ⟨hfalse,hvs⟩ | ⟨htrue,_⟩
    · exact False.elim (lt_asymm hsvlt hvs)
    · exact htrue
  · intro htrue
    rcases h with ⟨hfalse,hvs⟩ | ⟨_,hsvlt⟩
    · rw [htrue] at hfalse
      simp at hfalse
    · exact hsvlt

theorem source_lt_wholeCube_partner_iff_bit_false
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s v : V} {c : Fin n}
    (hsv : s ≠ v)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    v < s ↔ retainedBit C v c = false := by
  have h :=
    wholeCube_partner_order_of_source_bit
      C exponent hexp honeLoss hsv hvLoss hcV hwhole
  constructor
  · intro hvs
    rcases h with ⟨hfalse,_⟩ | ⟨htrue,hsvlt⟩
    · exact hfalse
    · exact False.elim (lt_asymm hvs hsvlt)
  · intro hfalse
    rcases h with ⟨_,hvs⟩ | ⟨htrue,hsvlt⟩
    · exact hvs
    · rw [hfalse] at htrue
      simp at htrue

theorem threeWholeCube_source_bit_order_partition
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
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hc1V : c₁ ∈ retainedActive C v)
    (hc2V : c₂ ∈ retainedActive C v)
    (hc3V : c₃ ∈ retainedActive C v)
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃) :
    (s₁ < v ↔ retainedBit C v c₁ = true) ∧
    (s₂ < v ↔ retainedBit C v c₂ = true) ∧
    (s₃ < v ↔ retainedBit C v c₃ = true) ∧
    (v < s₁ ↔ retainedBit C v c₁ = false) ∧
    (v < s₂ ↔ retainedBit C v c₂ = false) ∧
    (v < s₃ ↔ retainedBit C v c₃ = false) := by
  exact ⟨
    wholeCube_partner_lt_source_iff_bit_true
      C exponent hexp honeLoss hvs1.symm hvLoss hc1V h₁,
    wholeCube_partner_lt_source_iff_bit_true
      C exponent hexp honeLoss hvs2.symm hvLoss hc2V h₂,
    wholeCube_partner_lt_source_iff_bit_true
      C exponent hexp honeLoss hvs3.symm hvLoss hc3V h₃,
    source_lt_wholeCube_partner_iff_bit_false
      C exponent hexp honeLoss hvs1.symm hvLoss hc1V h₁,
    source_lt_wholeCube_partner_iff_bit_false
      C exponent hexp honeLoss hvs2.symm hvLoss hc2V h₂,
    source_lt_wholeCube_partner_iff_bit_false
      C exponent hexp honeLoss hvs3.symm hvLoss hc3V h₃
  ⟩

#print axioms wholeCube_partner_order_of_source_bit
#print axioms wholeCube_partner_lt_source_iff_bit_true
#print axioms source_lt_wholeCube_partner_iff_bit_false
#print axioms threeWholeCube_source_bit_order_partition

end OrderedEdgeColoring
end JSP000404Research
