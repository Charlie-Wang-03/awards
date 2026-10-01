import JSP000404Research.ResidualEnlargedLossCollisionGraph
import JSP000404Research.ResidualCandidateCollision
import Mathlib.Tactic

/-!
# Every loss vertex in a minimal enlarged-core exposes a translated collision

For a projected-loss vertex v in a minimal deficient enlarged candidate family,

  card(shared(v)) >= card(Q_v) + 1.

The original part Q_v contains only card(Q_v) words. Therefore at least one
shared word lies outside Q_v. Since the enlarged loss block is

  Q_v union allActiveTranslatedWords(v),

such a word necessarily lies in an active translated slice of v.

Hence every loss vertex in a minimal obstruction admits a concrete translated
collision with another candidate block in the same minimal core.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem minimal_enlargedCandidate_loss_has_shared_translated_word
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {v : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    ∃ word : Fin n → Bool,
      word ∈ sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v ∧
      word ∈ allActiveTranslatedWords C v ∧
      word ∉ retainedCompletionWords C v := by
  classical
  have hrequired :=
    minimal_enlargedCandidate_loss_shared_card_ge_cube_add_one
      C exponent hdef hmin hvT hvLoss hvLt
  by_contra hnone
  push_neg at hnone
  have hsub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      retainedCompletionWords C v := by
    intro word hshared
    have hparts := Finset.mem_inter.mp hshared
    have hvBlock :
        enlargedProjectedCandidateBlock C exponent v =
          allActiveLossCandidateBlock C v :=
      enlargedProjectedCandidateBlock_loss
        C exponent hvLoss
    rw [hvBlock] at hparts
    unfold allActiveLossCandidateBlock at hparts
    rcases Finset.mem_union.mp hparts.1 with hQ | hT
    · exact hQ
    · exfalso
      exact hnone word hshared hT
        (by
          intro hQ
          exact Finset.disjoint_left.mp
            (allActiveTranslatedWords_disjoint_original C v)
            hT hQ)
  have hcard :
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card
        ≤
      (retainedCompletionWords C v).card :=
    Finset.card_le_card hsub
  omega

theorem minimal_enlargedCandidate_loss_has_translated_collision
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {v : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    ∃ word : Fin n → Bool,
      ∃ c : Fin n,
        c ∈ retainedActive C v ∧
        word ∈ translatedCompletionWords C v c ∧
        ∃ w : V,
          w ∈ T ∧
          w ≠ v ∧
          word ∈ enlargedProjectedCandidateBlock C exponent w := by
  obtain ⟨word,hshared,htrans,hnotQ⟩ :=
    minimal_enlargedCandidate_loss_has_shared_translated_word
      C exponent hdef hmin hvT hvLoss hvLt
  unfold allActiveTranslatedWords at htrans
  obtain ⟨c,hcActive,hcWord⟩ :=
    Finset.mem_biUnion.mp htrans
  have hsharedData :=
    sharedBlockWords_has_other_block
      (enlargedProjectedCandidateBlock C exponent)
      hshared
  obtain ⟨_hvWord,w,hwT,hwv,hwWord⟩ := hsharedData
  exact ⟨word,c,hcActive,hcWord,w,hwT,hwv,hwWord⟩

#print axioms minimal_enlargedCandidate_loss_has_shared_translated_word
#print axioms minimal_enlargedCandidate_loss_has_translated_collision

end OrderedEdgeColoring
end JSP000404Research
