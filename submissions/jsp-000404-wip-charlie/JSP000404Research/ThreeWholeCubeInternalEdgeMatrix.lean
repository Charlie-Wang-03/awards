import JSP000404Research.ThreeWholeCubeOuterEdgeColour
import JSP000404Research.ResidualSecondLayerTripleCanonical
import Mathlib.Tactic

/-!
# Internal edge-colour matrix of a whole-cube star

Two same-source-bit whole-cube partners have a forced outer-edge colour:
for si<sj, false/false forces cj and true/true forces ci.

A source-partner owner-edge theorem is also recorded with an explicit
completion-word witness, avoiding any hidden nonemptiness assumption.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCube_source_partner_edge_owner_colour_of_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v s : V} {c : Fin n} {word : Fin n → Bool}
    (hvs : v ≠ s)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hcV : c ∈ retainedActive C v)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hwhole : WholeCubeQTPair C s v c) :
    (
      ∃ hlt : s < v,
      ∃ hret : (C.color s v).val < n,
        retainedColor C s v hret = c
    )
    ∨
    (
      ∃ hlt : v < s,
      ∃ hret : (C.color v s).val < n,
        retainedColor C v s hret = c
    ) := by
  have hvT :
      word ∈ translatedCompletionWords C v c := by
    rw [hwhole.2]
    exact hsQ
  have hsem :=
    QTT_owner_edge_semantics
      C exponent hexp honeLoss
      hvs.symm hvLoss hcV hsQ hvT
  rcases hsem with hleft | hright
  · obtain ⟨hsv,hret,hcol,_⟩ := hleft
    exact Or.inl ⟨hsv,hret,hcol⟩
  · obtain ⟨hvslt,hret,hcol,_⟩ := hright
    exact Or.inr ⟨hvslt,hret,hcol⟩

theorem wholeCube_partner_edge_eq_upper_owner_of_false_false
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v sᵢ sⱼ : V} {cᵢ cⱼ : Fin n}
    (hcij : cᵢ ≠ cⱼ)
    (hciV : cᵢ ∈ retainedActive C v)
    (hcjV : cⱼ ∈ retainedActive C v)
    (hi : WholeCubeQTPair C sᵢ v cᵢ)
    (hj : WholeCubeQTPair C sⱼ v cⱼ)
    (hij : sᵢ < sⱼ)
    (hret : (C.color sᵢ sⱼ).val < n)
    (hbitI : retainedBit C v cᵢ = false)
    (hbitJ : retainedBit C v cⱼ = false) :
    retainedColor C sᵢ sⱼ hret = cⱼ := by
  have htwo :=
    wholeCube_partner_pair_edge_colour_two_owner
      C hcij hciV hcjV hi hj
      (Or.inl ⟨hij,hret,True.intro⟩)
  rcases htwo with hforward | hreverse
  · obtain ⟨_,hret',hcol⟩ := hforward
    have hretEq : hret' = hret := Subsingleton.elim _ _
    subst hret'
    rcases hcol with hcolI | hcolJ
    · have hbits :=
        retained_edge_colour_bits_false_true C hij hret
      have hflipI :=
        (wholeCube_retainedCode_single_flip C hciV hi).2.1
      have hsameJ :=
        (wholeCube_retainedCode_single_flip C hcjV hj).2.2
          cᵢ hciV hcij
      rw [hcolI,hflipI,hsameJ,hbitI] at hbits
      simp at hbits
    · exact hcolJ
  · obtain ⟨hji,_,_⟩ := hreverse
    exact False.elim (lt_asymm hij hji)

theorem wholeCube_partner_edge_eq_lower_owner_of_true_true
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v sᵢ sⱼ : V} {cᵢ cⱼ : Fin n}
    (hcij : cᵢ ≠ cⱼ)
    (hciV : cᵢ ∈ retainedActive C v)
    (hcjV : cⱼ ∈ retainedActive C v)
    (hi : WholeCubeQTPair C sᵢ v cᵢ)
    (hj : WholeCubeQTPair C sⱼ v cⱼ)
    (hij : sᵢ < sⱼ)
    (hret : (C.color sᵢ sⱼ).val < n)
    (hbitI : retainedBit C v cᵢ = true)
    (hbitJ : retainedBit C v cⱼ = true) :
    retainedColor C sᵢ sⱼ hret = cᵢ := by
  have htwo :=
    wholeCube_partner_pair_edge_colour_two_owner
      C hcij hciV hcjV hi hj
      (Or.inl ⟨hij,hret,True.intro⟩)
  rcases htwo with hforward | hreverse
  · obtain ⟨_,hret',hcol⟩ := hforward
    have hretEq : hret' = hret := Subsingleton.elim _ _
    subst hret'
    rcases hcol with hcolI | hcolJ
    · exact hcolI
    · have hbits :=
        retained_edge_colour_bits_false_true C hij hret
      have hsameI :=
        (wholeCube_retainedCode_single_flip C hciV hi).2.2
          cⱼ hcjV hcij.symm
      have hflipJ :=
        (wholeCube_retainedCode_single_flip C hcjV hj).2.1
      rw [hcolJ,hsameI,hflipJ,hbitJ] at hbits
      simp at hbits
  · obtain ⟨hji,_,_⟩ := hreverse
    exact False.elim (lt_asymm hij hji)

#print axioms wholeCube_source_partner_edge_owner_colour_of_completion
#print axioms wholeCube_partner_edge_eq_upper_owner_of_false_false
#print axioms wholeCube_partner_edge_eq_lower_owner_of_true_true

end OrderedEdgeColoring
end JSP000404Research
