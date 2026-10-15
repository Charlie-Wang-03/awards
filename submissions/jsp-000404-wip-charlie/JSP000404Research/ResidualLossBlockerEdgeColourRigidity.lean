import JSP000404Research.ResidualLossTranslatedConflict
import JSP000404Research.ResidualLossCoveredExactTripleLedger
import Mathlib.Tactic

/-!
# Edge-colour rigidity of a genuinely covered translated projected-loss word

Let v be an actual projected-loss vertex: under the original one-layer
exponent and active-palette bounds it has NO residual-band incidence.

If flipping the retained coordinate c of an original completion word at v
produces a word covered by another vertex w, the edge {v,w} must be
retained and its ACTUAL colour must be precisely c.

Indeed, if this edge were residual, it would contradict the loss owner's
residual inactivity. If its retained colour e differed from c, flipping c
would preserve the bit at e, forcing both endpoints to have equal
canonical bits there; a retained edge forces opposite endpoint bits.

This necessary condition is stronger than "shared active coordinate" or
"opposite canonical bit at c." It does not claim that every edge-colour
c produces an actual covered word, nor does it establish global payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem loss_translated_blocker_edge_colour_eq_flip
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v c)
    (hw : word ∈ retainedCompletionWords C w) :
    (∃ hvwlt : v < w,
        ∃ hret : (C.color v w).val < n,
          retainedColor C v w hret = c) ∨
    (∃ hwvlt : w < v,
        ∃ hret : (C.color w v).val < n,
          retainedColor C w v hret = c) := by
  have hvInactive :=
    residual_inactive_of_mem_projectedLossVertices
      C exponent hexp honeLoss hvLoss
  have hvOrig :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hvT
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · left
    have hret : (C.color v w).val < n := by
      by_contra hnot
      have hres : IsResidual C v w := hnot
      exact hvInactive
        (residualCoord_mem_active_of_isResidual
          C hvwlt hres).1
    refine ⟨hvwlt, hret, ?_⟩
    let e : Fin n := retainedColor C v w hret
    have heV : e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_left C hvwlt hret
    have heW : e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_right C hvwlt hret
    by_contra hne
    have hec : e ≠ c := by simpa [e] using hne
    have hvAt :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word c)).1 hvOrig e heV
    have hwAt :=
      (mem_retainedCompletionWords C w word).1 hw e heW
    rw [flipBoolWordAt_off word hec] at hvAt
    have hbits : retainedBit C v e = retainedBit C w e :=
      hvAt.symm.trans hwAt
    exact (retainedBit_ne_of_retained_edge C hvwlt hret) hbits
  · right
    have hret : (C.color w v).val < n := by
      by_contra hnot
      have hres : IsResidual C w v := hnot
      exact hvInactive
        (residualCoord_mem_active_of_isResidual
          C hwvlt hres).2
    refine ⟨hwvlt, hret, ?_⟩
    let e : Fin n := retainedColor C w v hret
    have heW : e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_left C hwvlt hret
    have heV : e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_right C hwvlt hret
    by_contra hne
    have hec : e ≠ c := by simpa [e] using hne
    have hvAt :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word c)).1 hvOrig e heV
    have hwAt :=
      (mem_retainedCompletionWords C w word).1 hw e heW
    rw [flipBoolWordAt_off word hec] at hvAt
    have hbits : retainedBit C w e = retainedBit C v e :=
      hwAt.symm.trans hvAt
    exact (retainedBit_ne_of_retained_edge C hwvlt hret) hbits

#print axioms loss_translated_blocker_edge_colour_eq_flip

end OrderedEdgeColoring
end JSP000404Research
