import JSP000404Research.QTTEqualPaletteOrientationSwap
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# One-bit equal-palette Q/T pair: no off-owner coloured point in between

Let y and s have the same retained palette and differ in retained orientation
only at y's owner coordinate cy.  Let cx != cy be another active coordinate.

If both edges s-x and x-y are retained-coloured by cx, then x cannot lie
strictly between s and y.  Indeed, in either possible order the two cx-edges
make cx outgoing at one of s,y and incoming at the other, while the one-bit
Q/T relation says s and y have identical orientation at every coordinate
different from cy.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem not_between_equalPalette_QT_of_two_other_owner_edges
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s x y : V}
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hcxy : cx ≠ cy)
    (hactive :
      retainedActive C y = retainedActive C s)
    (hcyY : cy ∈ retainedActive C y)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hsxColour :
      (∃ hsx : s < x,
        ∃ hret : (C.color s x).val < n,
          retainedColor C s x hret = cx)
      ∨
      (∃ hxs : x < s,
        ∃ hret : (C.color x s).val < n,
          retainedColor C x s hret = cx))
    (hxyColour :
      (∃ hxy : x < y,
        ∃ hret : (C.color x y).val < n,
          retainedColor C x y hret = cx)
      ∨
      (∃ hyx : y < x,
        ∃ hret : (C.color y x).val < n,
          retainedColor C y x hret = cx)) :
    ¬ ((s < x ∧ x < y) ∨ (y < x ∧ x < s)) := by
  have hcode :=
    QTT_equal_palette_oneBit_code
      C hactive hcyY hsQ hyT
  have hcxS : cx ∈ retainedActive C s := by
    -- the concrete s-x edge supplies activity at s
    rcases hsxColour with h | h
    · obtain ⟨hsx,hret,hcol⟩ := h
      have hm :=
        retainedColor_mem_retainedActive_left C hsx hret
      simpa [hcol] using hm
    · obtain ⟨hxs,hret,hcol⟩ := h
      have hm :=
        retainedColor_mem_retainedActive_right C hxs hret
      simpa [hcol] using hm
  have hcxInEq :
      (cx ∈ incomingRetained C y ↔
        cx ∈ incomingRetained C s) := by
    apply incoming_membership_eq_off_oneBit C hcode.2
    · exact hcxS
    · exact hcxy

  rintro hbetween
  rcases hbetween with hbetween | hbetween
  · obtain ⟨hsx,hxy⟩ := hbetween
    have hsxC :
        ∃ hret : (C.color s x).val < n,
          retainedColor C s x hret = cx := by
      rcases hsxColour with h | h
      · exact ⟨h.choose_spec.choose,
          h.choose_spec.choose_spec⟩
      · exact False.elim (not_lt_of_ge hsx.le h.choose)
    have hxyC :
        ∃ hret : (C.color x y).val < n,
          retainedColor C x y hret = cx := by
      rcases hxyColour with h | h
      · exact ⟨h.choose_spec.choose,
          h.choose_spec.choose_spec⟩
      · exact False.elim (not_lt_of_ge hxy.le h.choose)
    obtain ⟨hretSX,hcolSX⟩ := hsxC
    obtain ⟨hretXY,hcolXY⟩ := hxyC
    have hOutS : cx ∈ outgoingRetained C s := by
      apply (mem_outgoingRetained_iff C s cx).2
      refine ⟨x,hsx,?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val hcolSX
      simpa [retainedColor] using hv
    have hInY : cx ∈ incomingRetained C y := by
      apply (mem_incomingRetained_iff C y cx).2
      refine ⟨x,hxy,?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val hcolXY
      simpa [retainedColor] using hv
    have hInS : cx ∈ incomingRetained C s :=
      hcxInEq.mp hInY
    exact Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C s)
      hInS hOutS
  · obtain ⟨hyx,hxs⟩ := hbetween
    have hxsC :
        ∃ hret : (C.color x s).val < n,
          retainedColor C x s hret = cx := by
      rcases hsxColour with h | h
      · exact False.elim (not_lt_of_ge hxs.le h.choose)
      · exact ⟨h.choose_spec.choose,
          h.choose_spec.choose_spec⟩
    have hyxC :
        ∃ hret : (C.color y x).val < n,
          retainedColor C y x hret = cx := by
      rcases hxyColour with h | h
      · exact False.elim (not_lt_of_ge hyx.le h.choose)
      · exact ⟨h.choose_spec.choose,
          h.choose_spec.choose_spec⟩
    obtain ⟨hretXS,hcolXS⟩ := hxsC
    obtain ⟨hretYX,hcolYX⟩ := hyxC
    have hInS : cx ∈ incomingRetained C s := by
      apply (mem_incomingRetained_iff C s cx).2
      refine ⟨x,hxs,?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val hcolXS
      simpa [retainedColor] using hv
    have hOutY : cx ∈ outgoingRetained C y := by
      apply (mem_outgoingRetained_iff C y cx).2
      refine ⟨x,hyx,?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val hcolYX
      simpa [retainedColor] using hv
    have hOutS : cx ∈ outgoingRetained C s := by
      -- active at s and the incoming-status equality tells us y is not
      -- incoming at cx because y is outgoing there.
      have hnotInY : cx ∉ incomingRetained C y := by
        intro h
        exact Finset.disjoint_left.mp
          (incomingRetained_disjoint_outgoingRetained C y)
          h hOutY
      have hnotInS : cx ∉ incomingRetained C s := by
        intro h
        exact hnotInY (hcxInEq.mpr h)
      rw [retainedActive_eq_incoming_union_outgoing C s] at hcxS
      rcases Finset.mem_union.mp hcxS with h | h
      · exact False.elim (hnotInS h)
      · exact h
    exact Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C s)
      hInS hOutS

#print axioms not_between_equalPalette_QT_of_two_other_owner_edges

end OrderedEdgeColoring
end JSP000404Research
