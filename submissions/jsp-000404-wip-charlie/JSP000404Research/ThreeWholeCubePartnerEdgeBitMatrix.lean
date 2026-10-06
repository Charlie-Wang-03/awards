import JSP000404Research.ThreeWholeCubeOuterEdgeColour
import Mathlib.Tactic

/-!
# Lightweight partner-edge bit matrix in a three-whole-cube star

For two whole-cube partners of a common source, the retained joining edge can
use only the two owner coordinates.  If the two source owner bits are both
false, the increasing partner edge uses the upper owner's coordinate.  If
both are true, it uses the lower owner's coordinate.

This module intentionally excludes the heavier Q/T source-partner semantics.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

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

#print axioms wholeCube_partner_edge_eq_upper_owner_of_false_false
#print axioms wholeCube_partner_edge_eq_lower_owner_of_true_true

end OrderedEdgeColoring
end JSP000404Research
