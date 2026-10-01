import JSP000404Research.ResidualActiveStarCandidate
import JSP000404Research.ResidualLossTranslatedConflict
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Global word-load bound for rich projected-loss stars

For one Boolean word y, consider projected-loss vertices v whose active-star
candidate block contains y.

At a fixed owner v, y belongs to at most one translated slice because the
active translated slices of v are pairwise disjoint.

Across distinct loss vertices, if y belongs to translated slices with the same
coordinate c, those two same-coordinate translated loss blocks are disjoint.
Hence the owner coordinates of translated occurrences are injective into
Fin n, so there are at most n translated-loss owners.

In addition, y belongs to at most two original completion cubes globally.

Therefore the number of projected-loss active-star blocks containing any fixed
Boolean word is at most n+2.  This is the bounded-load input for a rich-star
Hall route.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def translatedLossOwners
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool) : Finset V := by
  classical
  exact (projectedLossVertices C exponent).filter
    (fun v => word ∈ allActiveTranslatedWords C v)

theorem translatedLossOwner_has_unique_coordinate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {word : Fin n → Bool}
    {v : V}
    (hv : v ∈ translatedLossOwners C exponent word) :
    ∃! c : Fin n,
      c ∈ retainedActive C v ∧
      word ∈ translatedCompletionWords C v c := by
  classical
  have hvData := Finset.mem_filter.mp hv
  obtain ⟨c,hcActive,hcWord⟩ :=
    Finset.mem_biUnion.mp hvData.2
  refine ⟨c,⟨hcActive,hcWord⟩,?_⟩
  intro d hdData
  by_contra hdc
  have hdisj :=
    translatedCompletionWords_disjoint_of_distinct_active
      C hcActive hdData.1 hdc
  exact Finset.disjoint_left.mp hdisj hcWord hdData.2

noncomputable def translatedLossOwnerCoordinate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool)
    (v : V) : Fin n := by
  classical
  if hv : v ∈ translatedLossOwners C exponent word then
    exact Classical.choose
      (translatedLossOwner_has_unique_coordinate
        C exponent hv)
  else
    exact Classical.choice inferInstance

theorem translatedLossOwnerCoordinate_spec
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool)
    {v : V}
    (hv : v ∈ translatedLossOwners C exponent word) :
    translatedLossOwnerCoordinate C exponent word v
      ∈ retainedActive C v
    ∧
    word ∈ translatedCompletionWords C v
      (translatedLossOwnerCoordinate C exponent word v) := by
  classical
  simp [translatedLossOwnerCoordinate, hv]
  exact Classical.choose_spec
    (translatedLossOwner_has_unique_coordinate
      C exponent hv) |>.1

theorem translatedLossOwnerCoordinate_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (word : Fin n → Bool) :
    Set.InjOn
      (translatedLossOwnerCoordinate C exponent word)
      (translatedLossOwners C exponent word : Set V) := by
  intro v hv w hw hcoord
  by_contra hvw
  have hvData := Finset.mem_filter.mp hv
  have hwData := Finset.mem_filter.mp hw
  have hvSpec :=
    translatedLossOwnerCoordinate_spec
      C exponent word hv
  have hwSpec :=
    translatedLossOwnerCoordinate_spec
      C exponent word hw
  have hwWord' :
      word ∈ translatedCompletionWords C w
        (translatedLossOwnerCoordinate C exponent word v) := by
    simpa [hcoord] using hwSpec.2
  have hdisj :=
    translated_loss_blocks_disjoint_same_coordinate
      C exponent hexp honeLoss
      hvData.1 hwData.1 hvw
      (translatedLossOwnerCoordinate C exponent word v)
  exact Finset.disjoint_left.mp hdisj
    hvSpec.2 hwWord'

theorem translatedLossOwners_card_le_n
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (word : Fin n → Bool) :
    (translatedLossOwners C exponent word).card ≤ n := by
  classical
  have hinj :=
    translatedLossOwnerCoordinate_injective
      C exponent hexp honeLoss word
  have hmaps :
      Set.MapsTo
        (translatedLossOwnerCoordinate C exponent word)
        (translatedLossOwners C exponent word : Set V)
        ((Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
    intro v hv
    exact Finset.mem_univ _
  have hcard :
      (translatedLossOwners C exponent word).card ≤
        (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card_of_injOn
      (translatedLossOwnerCoordinate C exponent word)
      hmaps hinj
  simpa using hcard

noncomputable def lossStarOwners
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool) : Finset V := by
  classical
  exact (projectedLossVertices C exponent).filter
    (fun v => word ∈ activeStarCandidateBlock C v)

theorem lossStarOwners_subset_completion_union_translated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool) :
    lossStarOwners C exponent word ⊆
      completionFibre C word ∪
        translatedLossOwners C exponent word := by
  classical
  intro v hv
  have hvData := Finset.mem_filter.mp hv
  unfold activeStarCandidateBlock at hvData
  rcases Finset.mem_union.mp hvData.2 with hQ | hT
  · apply Finset.mem_union_left
    exact (mem_completionFibre C word v).2 hQ
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨hvData.1,hT⟩

theorem lossStarOwners_card_le_n_add_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (word : Fin n → Bool) :
    (lossStarOwners C exponent word).card ≤ n + 2 := by
  classical
  calc
    (lossStarOwners C exponent word).card
      ≤
    (completionFibre C word ∪
      translatedLossOwners C exponent word).card :=
        Finset.card_le_card
          (lossStarOwners_subset_completion_union_translated
            C exponent word)
    _ ≤
    (completionFibre C word).card +
      (translatedLossOwners C exponent word).card := by
        exact Finset.card_union_le _ _
    _ ≤ 2 + n := by
        omega
    _ = n + 2 := by omega

#print axioms translatedLossOwners_card_le_n
#print axioms lossStarOwners_card_le_n_add_two

end OrderedEdgeColoring
end JSP000404Research
