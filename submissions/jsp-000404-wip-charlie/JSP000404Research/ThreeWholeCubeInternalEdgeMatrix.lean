import JSP000404Research.ThreeWholeCubePartnerEdgeBitMatrix
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

#print axioms wholeCube_source_partner_edge_owner_colour_of_completion

end OrderedEdgeColoring
end JSP000404Research
