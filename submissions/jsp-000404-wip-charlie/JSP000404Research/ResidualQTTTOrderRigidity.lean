import JSP000404Research.ResidualSecondLayerTripleCanonical
import JSP000404Research.ResidualLossTranslatedConflict
import Mathlib.Tactic

/-!
# Order-rigid outer edges in a saturated Q/T/T/T star

For two translated owners x,y with distinct owner coordinates cx,cy, their
connecting retained edge has colour cx or cy.  The common Q-word at s fixes
the Boolean value of cx and cy according to which side of s each owner lies.

If x<y<s, colour cy would force the lower endpoint x to have incoming bit
true at cy, contradicting the translated completion constraint.  Hence the
edge colour is cx.  Symmetrically, if s<x<y, the edge colour is cy.

Thus on either side of s the outer edge uses the coordinate of the endpoint
farther from s.
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
    · have hcyX :
          cy ∈ retainedActive C x :=
        hcyCol ▸ retainedColor_mem_retainedActive_left C hxy hret
      have hbaseX :
          flipBoolWordAt word cx ∈ retainedCompletionWords C x :=
        (mem_translatedCompletionWords C x cx word).1 hxT
      have hbitX :=
        (mem_retainedCompletionWords C x
          (flipBoolWordAt word cx)).1 hbaseX cy hcyX
      have hflipOff :
          flipBoolWordAt word cx cy = word cy :=
        flipBoolWordAt_off word hcxy.symm
      rw [hflipOff] at hbitX
      have hwordCy :
          word cy = true := by
        have hsem :=
          QTT_owner_edge_semantics
            C exponent hexp honeLoss
            (ne_of_lt (hxy.trans hys))
            hyLoss hcy hsQ hyT
        rcases hsem with hleft | hright
        · exact hleft.2.2
        · exact False.elim (not_lt_of_ge (le_of_lt hys) hright.1)
      have hbitXTrue : retainedBit C x cy = true := by
        exact hbitX.symm.trans hwordCy
      have hcyIncoming :
          cy ∈ incomingRetained C x :=
        (mem_incomingRetained_iff_retainedBit_true C x cy).2
          hbitXTrue
      have hcyOutgoing :
          cy ∈ outgoingRetained C x := by
        have hleft :=
          retainedColor_mem_retainedActive_left C hxy hret
        have hnotIn : cy ∉ incomingRetained C x := by
          intro hin
          have hbit :=
            (mem_incomingRetained_iff_retainedBit_true C x cy).1 hin
          exact Bool.noConfusion
            (by simpa [hcyCol] using hbit)
        rw [retainedActive_eq_incoming_union_outgoing C x] at hleft
        rcases Finset.mem_union.mp hleft with hin | hout
        · exact False.elim (hnotIn hin)
        · simpa [hcyCol] using hout
      exact False.elim
        (Finset.disjoint_left.mp
          (incomingRetained_disjoint_outgoingRetained C x)
          hcyIncoming hcyOutgoing)
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
    · have hcxY :
          cx ∈ retainedActive C y :=
        hcxCol ▸ retainedColor_mem_retainedActive_right C hxy hret
      have hbaseY :
          flipBoolWordAt word cy ∈ retainedCompletionWords C y :=
        (mem_translatedCompletionWords C y cy word).1 hyT
      have hbitY :=
        (mem_retainedCompletionWords C y
          (flipBoolWordAt word cy)).1 hbaseY cx hcxY
      have hflipOff :
          flipBoolWordAt word cy cx = word cx :=
        flipBoolWordAt_off word hcxy
      rw [hflipOff] at hbitY
      have hwordCx :
          word cx = false := by
        have hsem :=
          QTT_owner_edge_semantics
            C exponent hexp honeLoss
            (ne_of_lt hsx)
            hxLoss hcx hsQ hxT
        rcases hsem with hleft | hright
        · exact False.elim (not_lt_of_ge (le_of_lt hsx) hleft.1)
        · exact hright.2.2
      have hbitYFalse : retainedBit C y cx = false := by
        exact hbitY.symm.trans hwordCx
      have hcxOut :
          cx ∈ outgoingRetained C y := by
        rw [retainedActive_eq_incoming_union_outgoing C y] at hcxY
        rcases Finset.mem_union.mp hcxY with hin | hout
        · have htrue :=
            (mem_incomingRetained_iff_retainedBit_true C y cx).1 hin
          rw [hbitYFalse] at htrue
          contradiction
        · exact hout
      have hcxIn :
          cx ∈ incomingRetained C y := by
        have hright :=
          retainedColor_mem_retainedActive_right C hxy hret
        have hbitTrue :
            retainedBit C y
              (retainedColor C x y hret) = true :=
          retainedBit_true_of_incomingRetained C
            (retainedColor_mem_incomingRetained_right C hxy hret)
        simpa [hcxCol] using
          (mem_incomingRetained_iff_retainedBit_true C y cx).2
            (by simpa [hcxCol] using hbitTrue)
      exact False.elim
        (Finset.disjoint_left.mp
          (incomingRetained_disjoint_outgoingRetained C y)
          hcxIn hcxOut)
    · exact ⟨hret,hcyCol⟩
  · exact False.elim (not_lt_of_ge (le_of_lt hxy) hbackward.1)

#print axioms QTT_same_left_side_outer_edge_eq_left_owner
#print axioms QTT_same_right_side_outer_edge_eq_right_owner

end OrderedEdgeColoring
end JSP000404Research
