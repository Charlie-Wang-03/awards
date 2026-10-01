import JSP000404Research.ResidualActiveStarCandidate
import JSP000404Research.ResidualLossBlockerEdge
import Mathlib.Tactic

/-!
# One ordinary blocker meets at most one translated slice of a loss star

Let v be projected-loss and w != v.  If Q_w intersects flip_c(Q_v), the actual
retained edge colour joining v and w is c.  Hence the same Q_w cannot intersect
flip_d(Q_v) for a distinct active coordinate d.

Therefore all translated-star words of v captured by one ordinary completion
cube Q_w lie in at most one translated slice.  Their total cardinality is at
most card(Q_v).

Since Q_v itself is disjoint from every other completion cube at a loss
vertex, the whole active-star candidate block of v meets Q_w in at most
card(Q_v) words.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem loss_blocker_cannot_meet_two_translated_slices
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
    (hcd : c ≠ d) :
    ¬ (
      (translatedCompletionWords C v c ∩
        retainedCompletionWords C w).Nonempty
      ∧
      (translatedCompletionWords C v d ∩
        retainedCompletionWords C w).Nonempty
    ) := by
  intro h
  obtain ⟨xc,hxcT,hxcW⟩ := h.1
  obtain ⟨xd,hxdT,hxdW⟩ := h.2
  have hcEdge :=
    loss_translated_blocker_edge_colour
      C exponent hexp honeLoss hvLoss hvw hc
      ((mem_translatedCompletionWords C v c xc).1 hxcT)
      (by simpa [flipBoolWordAt_involutive] using hxcW)
  have hdEdge :=
    loss_translated_blocker_edge_colour
      C exponent hexp honeLoss hvLoss hvw hd
      ((mem_translatedCompletionWords C v d xd).1 hxdT)
      (by simpa [flipBoolWordAt_involutive] using hxdW)
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · rcases hcEdge with hcRight | hcLeft
    · rcases hdEdge with hdRight | hdLeft
      · have hcEq := hcRight.2.2
        have hdEq := hdRight.2.2
        have : c = d := by
          rw [← hcEq, ← hdEq]
        exact hcd this
      · exact (not_lt_of_ge hvwlt.le) hdLeft.1
    · exact (not_lt_of_ge hvwlt.le) hcLeft.1
  · rcases hcEdge with hcRight | hcLeft
    · exact (not_lt_of_ge hwvlt.le) hcRight.1
    · rcases hdEdge with hdRight | hdLeft
      · exact (not_lt_of_ge hwvlt.le) hdRight.1
      · have hcEq := hcLeft.2.2
        have hdEq := hdLeft.2.2
        have : c = d := by
          rw [← hcEq, ← hdEq]
        exact hcd this

theorem loss_allActiveTranslated_inter_completion_card_le_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w) :
    (allActiveTranslatedWords C v ∩
      retainedCompletionWords C w).card
      ≤
    (retainedCompletionWords C v).card := by
  classical
  by_cases hnone :
      (allActiveTranslatedWords C v ∩
        retainedCompletionWords C w).Nonempty
  · obtain ⟨word,hwordStar,hwordW⟩ := hnone
    obtain ⟨c,hcActive,hwordC⟩ :=
      Finset.mem_biUnion.mp hwordStar
    have hsub :
        allActiveTranslatedWords C v ∩
            retainedCompletionWords C w
          ⊆
        translatedCompletionWords C v c := by
      intro y hy
      have hyStar := (Finset.mem_inter.mp hy).1
      have hyW := (Finset.mem_inter.mp hy).2
      obtain ⟨d,hdActive,hyD⟩ :=
        Finset.mem_biUnion.mp hyStar
      by_cases hdc : d = c
      · simpa [hdc] using hyD
      · exfalso
        exact loss_blocker_cannot_meet_two_translated_slices
          C exponent hexp honeLoss hvLoss hvw
          hdActive hcActive hdc
          ⟨⟨y,hyD,hyW⟩,⟨word,hwordC,hwordW⟩⟩
    calc
      (allActiveTranslatedWords C v ∩
        retainedCompletionWords C w).card
        ≤ (translatedCompletionWords C v c).card :=
          Finset.card_le_card hsub
      _ = (retainedCompletionWords C v).card :=
          translatedCompletionWords_card C v c
  · have hempty :
        allActiveTranslatedWords C v ∩
          retainedCompletionWords C w = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    rw [hempty]
    simp

theorem loss_activeStar_inter_completion_card_le_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w) :
    (activeStarCandidateBlock C v ∩
      retainedCompletionWords C w).card
      ≤
    (retainedCompletionWords C v).card := by
  classical
  have hQdisj :=
    projectedLoss_completion_disjoint
      C exponent hexp honeLoss hvLoss hvw
  have heq :
      activeStarCandidateBlock C v ∩
          retainedCompletionWords C w
        =
      allActiveTranslatedWords C v ∩
          retainedCompletionWords C w := by
    ext word
    simp only [activeStarCandidateBlock, Finset.mem_inter,
      Finset.mem_union]
    constructor
    · rintro ⟨hQ | hT, hw⟩
      · exact False.elim
          (Finset.disjoint_left.mp hQdisj hQ hw)
      · exact ⟨hT,hw⟩
    · rintro ⟨hT,hw⟩
      exact ⟨Or.inr hT,hw⟩
  rw [heq]
  exact loss_allActiveTranslated_inter_completion_card_le_owner
    C exponent hexp honeLoss hvLoss hvw

#print axioms loss_blocker_cannot_meet_two_translated_slices
#print axioms loss_allActiveTranslated_inter_completion_card_le_owner
#print axioms loss_activeStar_inter_completion_card_le_owner

end OrderedEdgeColoring
end JSP000404Research
