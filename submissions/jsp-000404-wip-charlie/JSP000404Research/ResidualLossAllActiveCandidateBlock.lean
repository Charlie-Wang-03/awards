import JSP000404Research.ResidualLossAllActiveSlices
import JSP000404Research.ResidualEnlargedCandidateCore
import JSP000404Research.ResidualLocalCandidateCapacity
import Mathlib.Tactic

/-!
# All-active translated candidate block at one projected-loss vertex

For one vertex v, collect the original retained completion cube Q_v together
with all one-coordinate translates along retained-active coordinates:

  B_all(v) = Q_v ∪ ⋃_{c ∈ retainedActive(v)} flip_c(Q_v).

The translated slices are pairwise disjoint, and every active translated slice
is disjoint from Q_v. Hence

  card B_all(v)
    = (card(retainedActive(v)) + 1) * card(Q_v).

For a projected-loss vertex, card(Q_v) = 2^(exponent(v)-1).  If in addition
exponent(v) < n, the projected-loss identity forces at least two retained-active
coordinates, so B_all(v) contains at least one complete Q_v of slack beyond
the target mass 2^exponent(v).
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem allActiveTranslatedWords_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    (allActiveTranslatedWords C v).card =
      (retainedActive C v).card *
        (retainedCompletionWords C v).card := by
  classical
  unfold allActiveTranslatedWords
  have hdisj :
      ∀ c ∈ retainedActive C v,
        ∀ d ∈ retainedActive C v,
          c ≠ d →
          Disjoint
            (translatedCompletionWords C v c)
            (translatedCompletionWords C v d) := by
    intro c hc d hd hcd
    exact translatedCompletionWords_disjoint_same_owner_distinct_active
      C hc hcd
  rw [Finset.card_biUnion hdisj]
  calc
    (∑ c ∈ retainedActive C v,
        (translatedCompletionWords C v c).card)
      =
    ∑ _c ∈ retainedActive C v,
        (retainedCompletionWords C v).card := by
      apply Finset.sum_congr rfl
      intro c hc
      exact translatedCompletionWords_card C v c
    _ =
      (retainedActive C v).card *
        (retainedCompletionWords C v).card := by
      simp

theorem allActiveTranslatedWords_disjoint_original
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    Disjoint
      (allActiveTranslatedWords C v)
      (retainedCompletionWords C v) := by
  classical
  rw [Finset.disjoint_left]
  intro word htrans horig
  unfold allActiveTranslatedWords at htrans
  obtain ⟨c,hcActive,hcWord⟩ := Finset.mem_biUnion.mp htrans
  exact Finset.disjoint_left.mp
    (translatedCompletionWords_disjoint_original_of_active C hcActive)
    hcWord horig

theorem allActiveLossCandidateBlock_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    (allActiveLossCandidateBlock C v).card =
      ((retainedActive C v).card + 1) *
        (retainedCompletionWords C v).card := by
  classical
  unfold allActiveLossCandidateBlock
  rw [Finset.card_union_of_disjoint
    (allActiveTranslatedWords_disjoint_original C v)]
  rw [allActiveTranslatedWords_card]
  omega

theorem projectedLoss_active_card_ge_two_of_exponent_lt_n
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    2 ≤ (retainedActive C v).card := by
  have hlossEq :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  unfold projectedFree at hlossEq
  have hcardLe :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  omega

theorem projectedLoss_allActiveBlock_target_plus_cube_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    2 ^ exponent v +
        (retainedCompletionWords C v).card
      ≤
    (allActiveLossCandidateBlock C v).card := by
  have hactive :
      2 ≤ (retainedActive C v).card :=
    projectedLoss_active_card_ge_two_of_exponent_lt_n
      C exponent hvLoss hvLt
  have hnonempty :
      (retainedActive C v).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨c,hc⟩ := hnonempty
  have hdouble :
      2 * (retainedCompletionWords C v).card =
        2 ^ exponent v := by
    have hblock :=
      projectedLoss_doubledBlock_card_eq_target
        C exponent hvLoss hc
    rw [doubledCompletionBlock_card_of_active C hc] at hblock
    exact hblock
  rw [allActiveLossCandidateBlock_card]
  rw [← hdouble]
  have hcoef :
      3 ≤ (retainedActive C v).card + 1 := by
    omega
  have hmul :=
    Nat.mul_le_mul_right
      (retainedCompletionWords C v).card hcoef
  omega

#print axioms allActiveTranslatedWords_card
#print axioms allActiveLossCandidateBlock_card
#print axioms projectedLoss_active_card_ge_two_of_exponent_lt_n
#print axioms projectedLoss_allActiveBlock_target_plus_cube_le

end OrderedEdgeColoring
end JSP000404Research
