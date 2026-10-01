import JSP000404Research.ResidualLossAllActiveIntersection
import JSP000404Research.ResidualLossTranslatedConflict
import JSP000404Research.ResidualLossDirectionalWitness
import Mathlib.Tactic

/-!
# Pairwise overlap bound for enlarged all-active loss blocks

Let v<w be two projected-loss vertices. Their connecting edge is retained; let
e be its retained colour.

Every collision between the enlarged all-active candidate blocks of v and w
lies in one of the two distinguished translated slices T_{v,e} or T_{w,e}.

Indeed:

* Q_v ∩ Q_w is empty;
* T_{v,c} ∩ Q_w forces c=e;
* Q_v ∩ T_{w,d} forces d=e;
* T_{v,c} ∩ T_{w,d} forces e=c or e=d.

Consequently

  card(B_all(v) ∩ B_all(w))
    <= card(Q_v) + card(Q_w).

Thus even though each loss vertex exposes all active translated slices, the
pairwise collision between two loss blocks remains confined to one slice from
each endpoint.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem loss_allActive_pair_intersection_subset_edge_slices_of_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvw : v < w)
    (hret : (C.color v w).val < n) :
    allActiveLossCandidateBlock C v ∩
        allActiveLossCandidateBlock C w
      ⊆
    translatedCompletionWords C v
        (retainedColor C v w hret)
      ∪
    translatedCompletionWords C w
        (retainedColor C v w hret) := by
  classical
  intro word hword
  have hparts := Finset.mem_inter.mp hword
  unfold allActiveLossCandidateBlock at hparts
  rcases Finset.mem_union.mp hparts.1 with hvQ | hvT
  · rcases Finset.mem_union.mp hparts.2 with hwQ | hwT
    · have hQQ :=
        projectedLoss_completion_disjoint
          C exponent hexp honeLoss hvLoss (ne_of_lt hvw)
      exact False.elim
        (Finset.disjoint_left.mp hQQ hvQ hwQ)
    · unfold allActiveTranslatedWords at hwT
      obtain ⟨d,hdActive,hdWord⟩ :=
        Finset.mem_biUnion.mp hwT
      have hdInter :
          (translatedCompletionWords C w d ∩
            retainedCompletionWords C v).Nonempty := by
        exact ⟨word,Finset.mem_inter.mpr ⟨hdWord,hvQ⟩⟩
      have hdEdge :=
        loss_translated_intersection_forces_edge_colour
          C exponent hexp honeLoss
          hwLoss (ne_of_gt hvw) hdActive hdInter
      rcases hdEdge with hright | hleft
      · exact False.elim ((not_lt_of_ge hvw.le) hright.1)
      · obtain ⟨_,hretD,hdEq⟩ := hleft
        have hvalD := congrArg Fin.val hdEq
        have hde :
            d = retainedColor C v w hret := by
          apply Fin.ext
          simpa [retainedColor] using hvalD
        apply Finset.mem_union_right
        simpa [hde] using hdWord
  · unfold allActiveTranslatedWords at hvT
    obtain ⟨c,hcActive,hcWord⟩ :=
      Finset.mem_biUnion.mp hvT
    rcases Finset.mem_union.mp hparts.2 with hwQ | hwT
    · have hcInter :
          (translatedCompletionWords C v c ∩
            retainedCompletionWords C w).Nonempty := by
        exact ⟨word,Finset.mem_inter.mpr ⟨hcWord,hwQ⟩⟩
      have hcEdge :=
        loss_translated_intersection_forces_edge_colour
          C exponent hexp honeLoss
          hvLoss (ne_of_lt hvw) hcActive hcInter
      rcases hcEdge with hright | hleft
      · obtain ⟨_,hretC,hcEq⟩ := hright
        have hvalC := congrArg Fin.val hcEq
        have hce :
            c = retainedColor C v w hret := by
          apply Fin.ext
          simpa [retainedColor] using hvalC
        apply Finset.mem_union_left
        simpa [hce] using hcWord
      · exact False.elim ((not_lt_of_ge hvw.le) hleft.1)
    · unfold allActiveTranslatedWords at hwT
      obtain ⟨d,hdActive,hdWord⟩ :=
        Finset.mem_biUnion.mp hwT
      have hedge :=
        translated_loss_conflict_edge_colour
          C exponent hexp honeLoss
          hvLoss hwLoss (ne_of_lt hvw)
          hcWord hdWord
      rcases hedge with hforward | hbackward
      · obtain ⟨_,hretE,hcol⟩ := hforward
        rcases hcol with hcEq | hdEq
        · have hvalC := congrArg Fin.val hcEq
          have hce :
              c = retainedColor C v w hret := by
            apply Fin.ext
            simpa [retainedColor] using hvalC
          apply Finset.mem_union_left
          simpa [hce] using hcWord
        · have hvalD := congrArg Fin.val hdEq
          have hde :
              d = retainedColor C v w hret := by
            apply Fin.ext
            simpa [retainedColor] using hvalD
          apply Finset.mem_union_right
          simpa [hde] using hdWord
      · exact False.elim ((not_lt_of_ge hvw.le) hbackward.1)

theorem loss_allActive_pair_intersection_card_le_sum_cubes_of_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvw : v < w) :
    (allActiveLossCandidateBlock C v ∩
      allActiveLossCandidateBlock C w).card
      ≤
    (retainedCompletionWords C v).card +
      (retainedCompletionWords C w).card := by
  have hret :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hvLoss hvw
  let e := retainedColor C v w hret
  have hsub :=
    loss_allActive_pair_intersection_subset_edge_slices_of_lt
      C exponent hexp honeLoss
      hvLoss hwLoss hvw hret
  calc
    (allActiveLossCandidateBlock C v ∩
        allActiveLossCandidateBlock C w).card
      ≤
    (translatedCompletionWords C v e ∪
      translatedCompletionWords C w e).card :=
      Finset.card_le_card hsub
    _ ≤
      (translatedCompletionWords C v e).card +
        (translatedCompletionWords C w e).card :=
      Finset.card_union_le
        (translatedCompletionWords C v e)
        (translatedCompletionWords C w e)
    _ =
      (retainedCompletionWords C v).card +
        (retainedCompletionWords C w).card := by
      rw [translatedCompletionWords_card,
          translatedCompletionWords_card]

theorem loss_allActive_pair_intersection_card_le_sum_cubes
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
    (allActiveLossCandidateBlock C v ∩
      allActiveLossCandidateBlock C w).card
      ≤
    (retainedCompletionWords C v).card +
      (retainedCompletionWords C w).card := by
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · exact loss_allActive_pair_intersection_card_le_sum_cubes_of_lt
      C exponent hexp honeLoss hvLoss hwLoss hvwlt
  · have h :=
      loss_allActive_pair_intersection_card_le_sum_cubes_of_lt
        C exponent hexp honeLoss hwLoss hvLoss hwvlt
    simpa [Finset.inter_comm, Nat.add_comm] using h

#print axioms loss_allActive_pair_intersection_subset_edge_slices_of_lt
#print axioms loss_allActive_pair_intersection_card_le_sum_cubes_of_lt
#print axioms loss_allActive_pair_intersection_card_le_sum_cubes

end OrderedEdgeColoring
end JSP000404Research
