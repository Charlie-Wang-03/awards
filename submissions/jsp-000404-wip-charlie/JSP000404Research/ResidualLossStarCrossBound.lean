import JSP000404Research.ResidualLossStarOrdinaryCollision
import JSP000404Research.ResidualLossTranslatedConflict
import Mathlib.Tactic

/-!
# Cross bound for two rich projected-loss Hamming stars

Let v,w be distinct projected-loss vertices and let e be their unique retained
edge colour.

Every collision between their active-star candidate blocks is forced onto one
of two cross arms:

* the e-translated slice of v;
* the e-translated slice of w.

Indeed original-original collision is impossible, original-translated
collision forces the translated coordinate to be e, and
translated-translated collision forces one of the two translated coordinates
to be e.

The two e-translated slices themselves are disjoint by the same-coordinate
loss-block theorem. Hence

  card (Star(v) ∩ Star(w)) <= card(Q_v) + card(Q_w).
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem loss_activeStar_inter_activeStar_subset_edge_cross
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w) :
    ∃ e : Fin n,
      e ∈ retainedActive C v ∧
      e ∈ retainedActive C w ∧
      activeStarCandidateBlock C v ∩
          activeStarCandidateBlock C w
        ⊆
      translatedCompletionWords C v e ∪
        translatedCompletionWords C w e := by
  classical
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · have hret : (C.color v w).val < n := by
      by_contra hnot
      have hres : IsResidual C v w := hnot
      have hvInactive :=
        residual_inactive_of_mem_projectedLossVertices
          C exponent hexp honeLoss hvLoss
      exact hvInactive
        (residualCoord_mem_active_of_isResidual
          C hvwlt hres).1
    let e : Fin n := retainedColor C v w hret
    have heV : e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_left C hvwlt hret
    have heW : e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_right C hvwlt hret
    refine ⟨e,heV,heW,?_⟩
    intro word hword
    have hparts := Finset.mem_inter.mp hword
    rcases Finset.mem_union.mp hparts.1 with hvQ | hvT
    · rcases Finset.mem_union.mp hparts.2 with hwQ | hwT
      · have hdisj :=
          projectedLoss_completion_disjoint
            C exponent hexp honeLoss hvLoss hvw
        exact False.elim
          (Finset.disjoint_left.mp hdisj hvQ hwQ)
      · obtain ⟨d,hdActive,hwTd⟩ :=
          Finset.mem_biUnion.mp hwT
        have hvOrigAsFlip :
            flipBoolWordAt word d ∈
              retainedCompletionWords C w :=
          (mem_translatedCompletionWords C w d word).1 hwTd
        have hedge :=
          loss_translated_blocker_edge_colour
            C exponent hexp honeLoss hwLoss hvw.symm
            hdActive hvOrigAsFlip
            (by simpa [flipBoolWordAt_involutive] using hvQ)
        rcases hedge with hright | hleft
        · exact False.elim ((not_lt_of_ge hvwlt.le) hright.1)
        · have hdEq : d = e := by
            apply Fin.ext
            have hval := congrArg Fin.val hleft.2.2
            simpa [e, retainedColor] using hval
          apply Finset.mem_union_right
          simpa [hdEq] using hwTd
    · obtain ⟨c,hcActive,hvTc⟩ :=
        Finset.mem_biUnion.mp hvT
      rcases Finset.mem_union.mp hparts.2 with hwQ | hwT
      · have hvOrig :
            flipBoolWordAt word c ∈
              retainedCompletionWords C v :=
          (mem_translatedCompletionWords C v c word).1 hvTc
        have hedge :=
          loss_translated_blocker_edge_colour
            C exponent hexp honeLoss hvLoss hvw
            hcActive hvOrig
            (by simpa [flipBoolWordAt_involutive] using hwQ)
        rcases hedge with hright | hleft
        · have hcEq : c = e := by
            apply Fin.ext
            have hval := congrArg Fin.val hright.2.2
            simpa [e, retainedColor] using hval
          apply Finset.mem_union_left
          simpa [hcEq] using hvTc
        · exact False.elim ((not_lt_of_ge hvwlt.le) hleft.1)
      · obtain ⟨d,hdActive,hwTd⟩ :=
          Finset.mem_biUnion.mp hwT
        have hedge :=
          translated_loss_conflict_edge_colour
            C exponent hexp honeLoss
            hvLoss hwLoss hvw hvTc hwTd
        rcases hedge with hright | hleft
        · obtain ⟨_hvw,hret',hcol⟩ := hright
          have hretEq : hret' = hret := Subsingleton.elim _ _
          subst hret'
          rcases hcol with hcEq | hdEq
          · apply Finset.mem_union_left
            simpa [e] using (show
              c = retainedColor C v w hret from hcEq.symm) ▸ hvTc
          · apply Finset.mem_union_right
            simpa [e] using (show
              d = retainedColor C v w hret from hdEq.symm) ▸ hwTd
        · exact False.elim ((not_lt_of_ge hvwlt.le) hleft.1)
  · have hret : (C.color w v).val < n := by
      by_contra hnot
      have hres : IsResidual C w v := hnot
      have hwInactive :=
        residual_inactive_of_mem_projectedLossVertices
          C exponent hexp honeLoss hwLoss
      exact hwInactive
        (residualCoord_mem_active_of_isResidual
          C hwvlt hres).1
    let e : Fin n := retainedColor C w v hret
    have heW : e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_left C hwvlt hret
    have heV : e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_right C hwvlt hret
    refine ⟨e,heV,heW,?_⟩
    intro word hword
    have hparts := Finset.mem_inter.mp hword
    rcases Finset.mem_union.mp hparts.1 with hvQ | hvT
    · rcases Finset.mem_union.mp hparts.2 with hwQ | hwT
      · have hdisj :=
          projectedLoss_completion_disjoint
            C exponent hexp honeLoss hvLoss hvw
        exact False.elim
          (Finset.disjoint_left.mp hdisj hvQ hwQ)
      · obtain ⟨d,hdActive,hwTd⟩ :=
          Finset.mem_biUnion.mp hwT
        have hwOrig :
            flipBoolWordAt word d ∈
              retainedCompletionWords C w :=
          (mem_translatedCompletionWords C w d word).1 hwTd
        have hedge :=
          loss_translated_blocker_edge_colour
            C exponent hexp honeLoss hwLoss hvw.symm
            hdActive hwOrig
            (by simpa [flipBoolWordAt_involutive] using hvQ)
        rcases hedge with hright | hleft
        · have hdEq : d = e := by
            apply Fin.ext
            have hval := congrArg Fin.val hright.2.2
            simpa [e, retainedColor] using hval
          apply Finset.mem_union_right
          simpa [hdEq] using hwTd
        · exact False.elim ((not_lt_of_ge hwvlt.le) hleft.1)
    · obtain ⟨c,hcActive,hvTc⟩ :=
        Finset.mem_biUnion.mp hvT
      rcases Finset.mem_union.mp hparts.2 with hwQ | hwT
      · have hvOrig :
            flipBoolWordAt word c ∈
              retainedCompletionWords C v :=
          (mem_translatedCompletionWords C v c word).1 hvTc
        have hedge :=
          loss_translated_blocker_edge_colour
            C exponent hexp honeLoss hvLoss hvw
            hcActive hvOrig
            (by simpa [flipBoolWordAt_involutive] using hwQ)
        rcases hedge with hright | hleft
        · exact False.elim ((not_lt_of_ge hwvlt.le) hright.1)
        · have hcEq : c = e := by
            apply Fin.ext
            have hval := congrArg Fin.val hleft.2.2
            simpa [e, retainedColor] using hval
          apply Finset.mem_union_left
          simpa [hcEq] using hvTc
      · obtain ⟨d,hdActive,hwTd⟩ :=
          Finset.mem_biUnion.mp hwT
        have hedge :=
          translated_loss_conflict_edge_colour
            C exponent hexp honeLoss
            hvLoss hwLoss hvw hvTc hwTd
        rcases hedge with hright | hleft
        · exact False.elim ((not_lt_of_ge hwvlt.le) hright.1)
        · obtain ⟨_hwv,hret',hcol⟩ := hleft
          have hretEq : hret' = hret := Subsingleton.elim _ _
          subst hret'
          rcases hcol with hcEq | hdEq
          · apply Finset.mem_union_left
            simpa [e] using (show
              c = retainedColor C w v hret from hcEq.symm) ▸ hvTc
          · apply Finset.mem_union_right
            simpa [e] using (show
              d = retainedColor C w v hret from hdEq.symm) ▸ hwTd

theorem loss_activeStar_inter_activeStar_card_le_owner_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w) :
    (activeStarCandidateBlock C v ∩
      activeStarCandidateBlock C w).card
      ≤
    (retainedCompletionWords C v).card +
      (retainedCompletionWords C w).card := by
  classical
  obtain ⟨e,heV,heW,hsub⟩ :=
    loss_activeStar_inter_activeStar_subset_edge_cross
      C exponent hexp honeLoss hvLoss hwLoss hvw
  calc
    (activeStarCandidateBlock C v ∩
      activeStarCandidateBlock C w).card
      ≤
    (translatedCompletionWords C v e ∪
      translatedCompletionWords C w e).card :=
        Finset.card_le_card hsub
    _ =
    (translatedCompletionWords C v e).card +
      (translatedCompletionWords C w e).card := by
        rw [Finset.card_union_of_disjoint]
        · rfl
        · exact translated_loss_blocks_disjoint_same_coordinate
            C exponent hexp honeLoss
            hvLoss hwLoss hvw e
    _ =
    (retainedCompletionWords C v).card +
      (retainedCompletionWords C w).card := by
        rw [translatedCompletionWords_card,
            translatedCompletionWords_card]

#print axioms loss_activeStar_inter_activeStar_subset_edge_cross
#print axioms loss_activeStar_inter_activeStar_card_le_owner_sum

end OrderedEdgeColoring
end JSP000404Research
