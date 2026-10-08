import JSP000404Research.ResidualLossTranslatedBlock
import JSP000404Research.ResidualInactiveUniqueCode
import Mathlib.Tactic

/-!
# Conflicts between translated blocks of projected-loss vertices

Projected-loss completion cubes are pairwise disjoint.  Translating two such
cubes by Boolean coordinate flips introduces the only new loss--loss
interactions.

Two basic rigidity facts hold.

* If the same coordinate c is used at two distinct loss vertices, the two
  translated cubes are still disjoint, because flip_c is a bijection and the
  original loss cubes are disjoint.

* More generally, if translated cubes flip coordinates c and d and intersect,
  then the connecting edge between the two loss vertices is retained and its
  retained colour must be c or d.  Otherwise the two preimage words agree at
  the retained edge colour, while the canonical endpoint bits at that edge
  colour are forced to differ.

Thus loss--loss translated conflicts are not arbitrary: every conflict edge
is labelled by one of the two endpoint flip witnesses.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translated_loss_blocks_disjoint_same_coordinate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    (c : Fin n) :
    Disjoint
      (translatedCompletionWords C v c)
      (translatedCompletionWords C w c) := by
  classical
  rw [Finset.disjoint_left]
  intro word hvT hwT
  have hvOrig :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hvT
  have hwOrig :
      flipBoolWordAt word c ∈ retainedCompletionWords C w :=
    (mem_translatedCompletionWords C w c word).1 hwT
  have hdisj :=
    projectedLoss_completion_disjoint
      C exponent hexp honeLoss hvLoss hvw
  exact Finset.disjoint_left.mp hdisj hvOrig hwOrig

theorem translated_loss_conflict_edge_colour
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {c d : Fin n}
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v c)
    (hwT : word ∈ translatedCompletionWords C w d) :
    (∃ hvwlt : v < w,
      ∃ hret : (C.color v w).val < n,
        retainedColor C v w hret = c ∨
        retainedColor C v w hret = d)
    ∨
    (∃ hwvlt : w < v,
      ∃ hret : (C.color w v).val < n,
        retainedColor C w v hret = c ∨
        retainedColor C w v hret = d) := by
  have hvInactive :=
    residual_inactive_of_mem_projectedLossVertices
      C exponent hexp honeLoss hvLoss
  have hwInactive :=
    residual_inactive_of_mem_projectedLossVertices
      C exponent hexp honeLoss hwLoss

  have hvOrig :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hvT
  have hwOrig :
      flipBoolWordAt word d ∈ retainedCompletionWords C w :=
    (mem_translatedCompletionWords C w d word).1 hwT

  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · left
    have hret : (C.color v w).val < n := by
      by_contra hnot
      have hres : IsResidual C v w := hnot
      exact hvInactive
        (residualCoord_mem_active_of_isResidual
          C hvwlt hres).1
    refine ⟨hvwlt,hret,?_⟩
    by_contra hne
    push_neg at hne
    let e : Fin n := retainedColor C v w hret
    have heV :
        e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_left
        C hvwlt hret
    have heW :
        e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_right
        C hvwlt hret
    have hvComp :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word c)).1 hvOrig
    have hwComp :=
      (mem_retainedCompletionWords C w
        (flipBoolWordAt word d)).1 hwOrig
    have hvAt := hvComp e heV
    have hwAt := hwComp e heW
    have hec : e ≠ c := by
      simpa [e] using hne.1
    have hed : e ≠ d := by
      simpa [e] using hne.2
    rw [flipBoolWordAt_off word hec] at hvAt
    rw [flipBoolWordAt_off word hed] at hwAt
    have hbits :
        retainedBit C v e = retainedBit C w e :=
      hvAt.symm.trans hwAt
    have hneBits :=
      retainedBit_ne_of_retained_edge
        C hvwlt hret
    exact hneBits hbits
  · right
    have hret : (C.color w v).val < n := by
      by_contra hnot
      have hres : IsResidual C w v := hnot
      exact hwInactive
        (residualCoord_mem_active_of_isResidual
          C hwvlt hres).1
    refine ⟨hwvlt,hret,?_⟩
    by_contra hne
    push_neg at hne
    let e : Fin n := retainedColor C w v hret
    have heW :
        e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_left
        C hwvlt hret
    have heV :
        e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_right
        C hwvlt hret
    have hvComp :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word c)).1 hvOrig
    have hwComp :=
      (mem_retainedCompletionWords C w
        (flipBoolWordAt word d)).1 hwOrig
    have hvAt := hvComp e heV
    have hwAt := hwComp e heW
    have hec : e ≠ c := by
      simpa [e] using hne.1
    have hed : e ≠ d := by
      simpa [e] using hne.2
    rw [flipBoolWordAt_off word hec] at hvAt
    rw [flipBoolWordAt_off word hed] at hwAt
    have hbits :
        retainedBit C w e = retainedBit C v e :=
      hwAt.symm.trans hvAt
    have hneBits :=
      retainedBit_ne_of_retained_edge
        C hwvlt hret
    exact hneBits hbits

theorem translated_loss_conflict_distinct_coordinates
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {c d : Fin n}
    (hoverlap :
      (translatedCompletionWords C v c ∩
        translatedCompletionWords C w d).Nonempty) :
    c ≠ d := by
  intro hcd
  subst d
  obtain ⟨word,hword⟩ := hoverlap
  obtain ⟨hvT,hwT⟩ := Finset.mem_inter.mp hword
  exact Finset.disjoint_left.mp
    (translated_loss_blocks_disjoint_same_coordinate
      C exponent hexp honeLoss hvLoss hwLoss hvw c)
    hvT hwT

#print axioms translated_loss_blocks_disjoint_same_coordinate
#print axioms translated_loss_conflict_edge_colour
#print axioms translated_loss_conflict_distinct_coordinates

end OrderedEdgeColoring
end JSP000404Research
