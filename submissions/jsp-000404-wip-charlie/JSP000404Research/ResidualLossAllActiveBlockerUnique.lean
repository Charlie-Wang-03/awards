import JSP000404Research.ResidualLossAllActiveCandidateBlock
import JSP000404Research.ResidualLossBlockerEdge
import Mathlib.Tactic

/-!
# A fixed blocker sees at most one active translated slice of a loss owner

Let v be projected-loss and w != v.  If Q_w intersects the translated slice
flip_c(Q_v), then the actual retained colour on edge vw is c.

Hence Q_w cannot intersect two distinct active translated slices of v: the
single edge vw has only one retained colour.

This is the key cross-vertex rigidity for the enlarged all-active loss
candidate block.  Although the loss block contains many translated slices,
each fixed external completion cube can collide with at most one of them.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem loss_translated_intersection_forces_edge_colour
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hinter :
      (translatedCompletionWords C v c ∩
        retainedCompletionWords C w).Nonempty) :
    (
      ∃ hvwlt : v < w,
        ∃ hret : (C.color v w).val < n,
          retainedColor C v w hret = c
    )
    ∨
    (
      ∃ hwvlt : w < v,
        ∃ hret : (C.color w v).val < n,
          retainedColor C w v hret = c
    ) := by
  obtain ⟨word,hword⟩ := hinter
  have hparts := Finset.mem_inter.mp hword
  have hsrc :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hparts.1
  have hw :
      flipBoolWordAt (flipBoolWordAt word c) c ∈
        retainedCompletionWords C w := by
    simpa [flipBoolWordAt_involutive] using hparts.2
  exact loss_translated_blocker_edge_colour
    C exponent hexp honeLoss
    hvLoss hvw hc hsrc hw

theorem loss_fixed_blocker_translated_coordinate_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C v)
    (hcInter :
      (translatedCompletionWords C v c ∩
        retainedCompletionWords C w).Nonempty)
    (hdInter :
      (translatedCompletionWords C v d ∩
        retainedCompletionWords C w).Nonempty) :
    c = d := by
  have hcEdge :=
    loss_translated_intersection_forces_edge_colour
      C exponent hexp honeLoss hvLoss hvw hc hcInter
  have hdEdge :=
    loss_translated_intersection_forces_edge_colour
      C exponent hexp honeLoss hvLoss hvw hd hdInter
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · rcases hcEdge with hcR | hcL
    · rcases hdEdge with hdR | hdL
      · obtain ⟨_,hretC,hcEq⟩ := hcR
        obtain ⟨_,hretD,hdEq⟩ := hdR
        have hvalC : (C.color v w).val = c.val := by
          simpa [retainedColor] using congrArg Fin.val hcEq
        have hvalD : (C.color v w).val = d.val := by
          simpa [retainedColor] using congrArg Fin.val hdEq
        exact Fin.ext (hvalC.symm.trans hvalD)
      · exact False.elim ((not_lt_of_ge hvwlt.le) hdL.1)
    · exact False.elim ((not_lt_of_ge hvwlt.le) hcL.1)
  · rcases hcEdge with hcR | hcL
    · exact False.elim ((not_lt_of_ge hwvlt.le) hcR.1)
    · rcases hdEdge with hdR | hdL
      · exact False.elim ((not_lt_of_ge hwvlt.le) hdR.1)
      · obtain ⟨_,hretC,hcEq⟩ := hcL
        obtain ⟨_,hretD,hdEq⟩ := hdL
        have hvalC : (C.color w v).val = c.val := by
          simpa [retainedColor] using congrArg Fin.val hcEq
        have hvalD : (C.color w v).val = d.val := by
          simpa [retainedColor] using congrArg Fin.val hdEq
        exact Fin.ext (hvalC.symm.trans hvalD)

#print axioms loss_translated_intersection_forces_edge_colour
#print axioms loss_fixed_blocker_translated_coordinate_unique

end OrderedEdgeColoring
end JSP000404Research
