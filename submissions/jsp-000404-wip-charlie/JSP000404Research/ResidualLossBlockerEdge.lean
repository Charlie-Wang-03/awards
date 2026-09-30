import JSP000404Research.ResidualLossTranslatedBlock
import JSP000404Research.ResidualInactiveUniqueCode
import JSP000404Research.ResidualSameCodeOrientation
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# Exact retained-edge geometry of a translated loss blocker

Let v be a projected-loss vertex, let c be retained-active at v, and let

  x ∈ Q_v,  y = flip_c(x).

If y lies in another completion cube Q_w, then the actual retained edge joining
v and w has colour c.

Indeed v is residual-inactive, so the joining edge is retained. If its retained
colour e differed from c, then x and y agree at e, while completion membership
would force that common bit to equal the two opposite canonical endpoint bits.

Consequently blocker geometry is one-sided:

* if c is outgoing at v / retainedBit(v,c)=false, every blocker satisfies v<w;
* if c is incoming at v / retainedBit(v,c)=true, every blocker satisfies w<v.

Thus each translated loss block can only be obstructed along the monochromatic
c-star incident to its owner.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem loss_translated_blocker_edge_colour
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    (hw :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    (∃ hvwlt : v < w,
      ∃ hret : (C.color v w).val < n,
        retainedColor C v w hret = c)
    ∨
    (∃ hwvlt : w < v,
      ∃ hret : (C.color w v).val < n,
        retainedColor C w v hret = c) := by
  have hvInactive :=
    residual_inactive_of_mem_projectedLossVertices
      C exponent hexp honeLoss hvLoss
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · left
    have hret : (C.color v w).val < n := by
      by_contra hnot
      have hres : IsResidual C v w := hnot
      exact hvInactive
        (residualCoord_mem_active_of_isResidual
          C hvwlt hres).1
    refine ⟨hvwlt,hret,?_⟩
    let e : Fin n := retainedColor C v w hret
    by_contra hec
    have heV :
        e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_left
        C hvwlt hret
    have heW :
        e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_right
        C hvwlt hret
    have hvComp :=
      (mem_retainedCompletionWords C v word).1 hword
    have hwComp :=
      (mem_retainedCompletionWords C w
        (flipBoolWordAt word c)).1 hw
    have hvAt := hvComp e heV
    have hwAt := hwComp e heW
    have hec' : e ≠ c := by
      intro h
      exact hec (by simpa [e] using h)
    rw [flipBoolWordAt_off word hec'] at hwAt
    have hbits :
        retainedBit C v e = retainedBit C w e :=
      hvAt.symm.trans hwAt
    exact
      (retainedBit_ne_of_retained_edge C hvwlt hret) hbits
  · right
    have hret : (C.color w v).val < n := by
      by_contra hnot
      have hres : IsResidual C w v := hnot
      exact hvInactive
        (residualCoord_mem_active_of_isResidual
          C hwvlt hres).2
    refine ⟨hwvlt,hret,?_⟩
    let e : Fin n := retainedColor C w v hret
    by_contra hec
    have heW :
        e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_left
        C hwvlt hret
    have heV :
        e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_right
        C hwvlt hret
    have hvComp :=
      (mem_retainedCompletionWords C v word).1 hword
    have hwComp :=
      (mem_retainedCompletionWords C w
        (flipBoolWordAt word c)).1 hw
    have hvAt := hvComp e heV
    have hwAt := hwComp e heW
    have hec' : e ≠ c := by
      intro h
      exact hec (by simpa [e] using h)
    rw [flipBoolWordAt_off word hec'] at hwAt
    have hbits :
        retainedBit C w e = retainedBit C v e :=
      hwAt.symm.trans hvAt
    exact
      (retainedBit_ne_of_retained_edge C hwvlt hret) hbits

theorem loss_translated_blocker_right_of_outgoing
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hcOut : c ∈ outgoingRetained C v)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    (hw :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    v < w := by
  rcases loss_translated_blocker_edge_colour
      C exponent hexp honeLoss hvLoss hvw hc hword hw
    with hright | hleft
  · exact hright.1
  · obtain ⟨hwvlt,hret,hcol⟩ := hleft
    have hcIn : c ∈ incomingRetained C v := by
      apply (mem_incomingRetained_iff C v c).2
      refine ⟨w,hwvlt,?_⟩
      apply Fin.ext
      have hval := congrArg Fin.val hcol
      simpa [retainedColor] using hval
    exact False.elim
      (Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C v)
        hcIn hcOut)

theorem loss_translated_blocker_left_of_incoming
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hcIn : c ∈ incomingRetained C v)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    (hw :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    w < v := by
  rcases loss_translated_blocker_edge_colour
      C exponent hexp honeLoss hvLoss hvw hc hword hw
    with hright | hleft
  · obtain ⟨hvwlt,hret,hcol⟩ := hright
    have hcOut : c ∈ outgoingRetained C v := by
      apply (mem_outgoingRetained_iff C v c).2
      refine ⟨w,hvwlt,?_⟩
      apply Fin.ext
      have hval := congrArg Fin.val hcol
      simpa [retainedColor] using hval
    exact False.elim
      (Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C v)
        hcIn hcOut)
  · exact hleft.1

theorem loss_translated_blocker_side_of_retainedBit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    (hw :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    (retainedBit C v c = false ∧ v < w)
    ∨
    (retainedBit C v c = true ∧ w < v) := by
  by_cases hb : retainedBit C v c = false
  · left
    refine ⟨hb,?_⟩
    have hcOut :
        c ∈ outgoingRetained C v := by
      rw [retainedActive_eq_incoming_union_outgoing C v] at hc
      rcases Finset.mem_union.mp hc with hcIn | hcOut
      · have htrue :=
          (mem_incomingRetained_iff_retainedBit_true C v c).1 hcIn
        rw [hb] at htrue
        contradiction
      · exact hcOut
    exact loss_translated_blocker_right_of_outgoing
      C exponent hexp honeLoss hvLoss hvw hc hcOut hword hw
  · have hbTrue : retainedBit C v c = true := by
      cases h : retainedBit C v c <;> simp_all
    right
    refine ⟨hbTrue,?_⟩
    have hcIn :
        c ∈ incomingRetained C v :=
      (mem_incomingRetained_iff_retainedBit_true C v c).2 hbTrue
    exact loss_translated_blocker_left_of_incoming
      C exponent hexp honeLoss hvLoss hvw hc hcIn hword hw

#print axioms loss_translated_blocker_edge_colour
#print axioms loss_translated_blocker_right_of_outgoing
#print axioms loss_translated_blocker_left_of_incoming
#print axioms loss_translated_blocker_side_of_retainedBit

end OrderedEdgeColoring
end JSP000404Research
