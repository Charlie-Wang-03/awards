import JSP000404Research.ResidualLossAllActiveBlockerUnique
import Mathlib.Tactic

/-!
# Intersection bound for the enlarged all-active loss block

For a projected-loss owner v and any external vertex w != v, the completion
cube Q_w can meet at most one active translated slice of v.  Since every such
slice has cardinality |Q_v|,

  card((⋃ active c, T_{v,c}) ∩ Q_w) <= |Q_v|.

The original loss cube Q_v is disjoint from Q_w, so the same bound holds for
the entire enlarged candidate block

  Q_v ∪ ⋃ active c, T_{v,c}.

Because a projected-loss target has mass 2|Q_v|, every single external
completion cube captures at most half of the loss target mass from this
enlarged block.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem allActiveTranslated_inter_blocker_card_le_cube
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
  by_cases hinter :
      (allActiveTranslatedWords C v ∩
        retainedCompletionWords C w).Nonempty
  · obtain ⟨base,hbase⟩ := hinter
    have hbaseParts := Finset.mem_inter.mp hbase
    unfold allActiveTranslatedWords at hbaseParts
    obtain ⟨c,hcActive,hbaseC⟩ :=
      Finset.mem_biUnion.mp hbaseParts.1
    have hcInter :
        (translatedCompletionWords C v c ∩
          retainedCompletionWords C w).Nonempty := by
      exact ⟨base,Finset.mem_inter.mpr
        ⟨hbaseC,hbaseParts.2⟩⟩
    have hsub :
        allActiveTranslatedWords C v ∩
            retainedCompletionWords C w
          ⊆
        translatedCompletionWords C v c := by
      intro word hword
      have hparts := Finset.mem_inter.mp hword
      unfold allActiveTranslatedWords at hparts
      obtain ⟨d,hdActive,hwordD⟩ :=
        Finset.mem_biUnion.mp hparts.1
      have hdInter :
          (translatedCompletionWords C v d ∩
            retainedCompletionWords C w).Nonempty := by
        exact ⟨word,Finset.mem_inter.mpr
          ⟨hwordD,hparts.2⟩⟩
      have hdc :=
        loss_fixed_blocker_translated_coordinate_unique
          C exponent hexp honeLoss
          hvLoss hvw hdActive hcActive hdInter hcInter
      simpa [hdc] using hwordD
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
      Finset.not_nonempty_iff_eq_empty.mp hinter
    rw [hempty]
    simp

theorem allActiveLossCandidateBlock_inter_blocker_card_le_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w) :
    (allActiveLossCandidateBlock C v ∩
      retainedCompletionWords C w).card
      ≤
    (retainedCompletionWords C v).card := by
  classical
  have hQQ :=
    projectedLoss_completion_disjoint
      C exponent hexp honeLoss hvLoss hvw
  have hsub :
      allActiveLossCandidateBlock C v ∩
          retainedCompletionWords C w
        ⊆
      allActiveTranslatedWords C v ∩
          retainedCompletionWords C w := by
    intro word hword
    have hparts := Finset.mem_inter.mp hword
    unfold allActiveLossCandidateBlock at hparts
    rcases Finset.mem_union.mp hparts.1 with hQ | hT
    · exact False.elim
        (Finset.disjoint_left.mp hQQ hQ hparts.2)
    · exact Finset.mem_inter.mpr ⟨hT,hparts.2⟩
  calc
    (allActiveLossCandidateBlock C v ∩
        retainedCompletionWords C w).card
      ≤
    (allActiveTranslatedWords C v ∩
        retainedCompletionWords C w).card :=
      Finset.card_le_card hsub
    _ ≤ (retainedCompletionWords C v).card :=
      allActiveTranslated_inter_blocker_card_le_cube
        C exponent hexp honeLoss hvLoss hvw

theorem projectedLoss_single_blocker_captures_at_most_half_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w) :
    2 * (allActiveLossCandidateBlock C v ∩
      retainedCompletionWords C w).card
      ≤
    2 ^ exponent v := by
  have hinter :=
    allActiveLossCandidateBlock_inter_blocker_card_le_cube
      C exponent hexp honeLoss hvLoss hvw
  have hlossEq :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  rw [retainedCompletionWords_card] at hinter
  unfold projectedFree at hlossEq
  rw [hlossEq, pow_succ]
  have hmul := Nat.mul_le_mul_left 2 hinter
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

#print axioms allActiveTranslated_inter_blocker_card_le_cube
#print axioms allActiveLossCandidateBlock_inter_blocker_card_le_cube
#print axioms projectedLoss_single_blocker_captures_at_most_half_target

end OrderedEdgeColoring
end JSP000404Research
