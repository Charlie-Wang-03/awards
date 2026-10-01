import JSP000404Research.ResidualSecondLayerTripleCanonical
import JSP000404Research.ResidualLossTranslatedConflict
import Mathlib.Tactic

/-!
# Order-rigid outer edges in a saturated Q/T/T/T star

For two translated owners x,y with distinct owner coordinates cx,cy, their
connecting retained edge has colour cx or cy.

If x<y<s, colour cy would agree with the Q/T edge y-s, producing a forbidden
monochromatic increasing two-path x<y<s. Hence x-y has colour cx.

Symmetrically, if s<x<y, colour cx would agree with the Q/T edge s-x,
producing a forbidden monochromatic increasing two-path s<x<y. Hence x-y has
colour cy.

Thus on either side of the completion owner s, the outer edge uses the owner
coordinate of the endpoint farther from s.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem QTT_same_left_side_outer_edge_eq_left_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y : V}
    (hxy : x < y)
    (hys : y < s)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcxy : cx ≠ cy)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy) :
    ∃ hret : (C.color x y).val < n,
      retainedColor C x y hret = cx := by
  have hconf :=
    translated_loss_conflict_edge_colour
      C exponent hexp honeLoss
      hxLoss hyLoss (ne_of_lt hxy)
      hxT hyT
  rcases hconf with hforward | hbackward
  · obtain ⟨_hxy,hret,hcol⟩ := hforward
    rcases hcol with hcxCol | hcyCol
    · exact ⟨hret,hcxCol⟩
    · have hysSem :=
        QTT_owner_edge_semantics
          C exponent hexp honeLoss
          (ne_of_lt hys).symm
          hyLoss hcy hsQ hyT
      rcases hysSem with hleft | hright
      · obtain ⟨hys',hretYS,hcolYS,_hword⟩ := hleft
        have hfullXY :
            C.color x y = cy.castSucc := by
          apply Fin.ext
          have hv := congrArg Fin.val hcyCol
          simpa [retainedColor] using hv
        have hfullYS :
            C.color y s = cy.castSucc := by
          apply Fin.ext
          have hv := congrArg Fin.val hcolYS
          simpa [retainedColor] using hv
        apply False.elim
        apply C.noMonoTwoPath hxy hys
        rw [hfullXY,hfullYS]
      · exact False.elim (not_lt_of_ge (le_of_lt hys) hright.1)
  · exact False.elim (not_lt_of_ge (le_of_lt hxy) hbackward.1)

theorem QTT_same_right_side_outer_edge_eq_right_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y : V}
    (hsx : s < x)
    (hxy : x < y)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcxy : cx ≠ cy)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy) :
    ∃ hret : (C.color x y).val < n,
      retainedColor C x y hret = cy := by
  have hconf :=
    translated_loss_conflict_edge_colour
      C exponent hexp honeLoss
      hxLoss hyLoss (ne_of_lt hxy)
      hxT hyT
  rcases hconf with hforward | hbackward
  · obtain ⟨_hxy,hret,hcol⟩ := hforward
    rcases hcol with hcxCol | hcyCol
    · have hsxSem :=
        QTT_owner_edge_semantics
          C exponent hexp honeLoss
          (ne_of_lt hsx)
          hxLoss hcx hsQ hxT
      rcases hsxSem with hleft | hright
      · exact False.elim (not_lt_of_ge (le_of_lt hsx) hleft.1)
      · obtain ⟨hsx',hretSX,hcolSX,_hword⟩ := hright
        have hfullSX :
            C.color s x = cx.castSucc := by
          apply Fin.ext
          have hv := congrArg Fin.val hcolSX
          simpa [retainedColor] using hv
        have hfullXY :
            C.color x y = cx.castSucc := by
          apply Fin.ext
          have hv := congrArg Fin.val hcxCol
          simpa [retainedColor] using hv
        apply False.elim
        apply C.noMonoTwoPath hsx hxy
        rw [hfullSX,hfullXY]
    · exact ⟨hret,hcyCol⟩
  · exact False.elim (not_lt_of_ge (le_of_lt hxy) hbackward.1)

#print axioms QTT_same_left_side_outer_edge_eq_left_owner
#print axioms QTT_same_right_side_outer_edge_eq_right_owner

end OrderedEdgeColoring
end JSP000404Research
