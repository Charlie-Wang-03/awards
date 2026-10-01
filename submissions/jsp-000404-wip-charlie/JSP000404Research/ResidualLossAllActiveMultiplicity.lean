import JSP000404Research.ResidualLossAllActivePairOverlap
import JSP000404Research.ResidualLossTranslatedConflict
import Mathlib.Tactic

/-!
# Multiplicity of all-active translated loss coverage

Fix a Boolean word y.  Consider projected-loss vertices v for which y lies in
at least one active translated slice T_{v,c}.

At a fixed owner v the active translated slices are pairwise disjoint, so the
responsible coordinate is unique.  Across distinct loss owners, equal
responsible coordinates are impossible because translated loss blocks at the
same coordinate are disjoint.

Therefore the responsible-coordinate map injects the translated loss fibre
into Fin n, and any Boolean word belongs to translated slices of at most n
projected-loss owners.

This extends the earlier fixed-choice fibre bound to the enlarged all-active
candidate family, where the responsible coordinate is chosen canonically from
the actual word membership.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def allActiveTranslatedLossFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool) : Finset V := by
  classical
  exact (projectedLossVertices C exponent).filter
    (fun v => word ∈ allActiveTranslatedWords C v)

@[simp] theorem mem_allActiveTranslatedLossFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool)
    (v : V) :
    v ∈ allActiveTranslatedLossFibre C exponent word ↔
      v ∈ projectedLossVertices C exponent ∧
      word ∈ allActiveTranslatedWords C v := by
  classical
  simp [allActiveTranslatedLossFibre]

noncomputable def allActiveTranslatedFibreCoordinate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool)
    (x : {v : V //
      v ∈ allActiveTranslatedLossFibre C exponent word}) :
    Fin n := by
  classical
  have hx :=
    (mem_allActiveTranslatedLossFibre
      C exponent word x.1).1 x.2
  unfold allActiveTranslatedWords at hx
  exact Classical.choose
    (show ∃ c ∈ retainedActive C x.1,
        word ∈ translatedCompletionWords C x.1 c by
      simpa only [Finset.mem_biUnion] using hx.2)

theorem allActiveTranslatedFibreCoordinate_spec
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool)
    (x : {v : V //
      v ∈ allActiveTranslatedLossFibre C exponent word}) :
    allActiveTranslatedFibreCoordinate C exponent word x ∈
        retainedActive C x.1
    ∧
    word ∈ translatedCompletionWords C x.1
      (allActiveTranslatedFibreCoordinate C exponent word x) := by
  classical
  have hx :=
    (mem_allActiveTranslatedLossFibre
      C exponent word x.1).1 x.2
  unfold allActiveTranslatedWords at hx
  have hex :
      ∃ c ∈ retainedActive C x.1,
        word ∈ translatedCompletionWords C x.1 c := by
    simpa only [Finset.mem_biUnion] using hx.2
  exact Classical.choose_spec hex

theorem allActiveTranslatedFibreCoordinate_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (word : Fin n → Bool) :
    Function.Injective
      (allActiveTranslatedFibreCoordinate C exponent word) := by
  classical
  intro x y hcoord
  apply Subtype.ext
  by_contra hxy
  have hxData :=
    (mem_allActiveTranslatedLossFibre
      C exponent word x.1).1 x.2
  have hyData :=
    (mem_allActiveTranslatedLossFibre
      C exponent word y.1).1 y.2
  have hxSpec :=
    allActiveTranslatedFibreCoordinate_spec
      C exponent word x
  have hySpec :=
    allActiveTranslatedFibreCoordinate_spec
      C exponent word y
  have hdisj :=
    translated_loss_blocks_disjoint_same_coordinate
      C exponent hexp honeLoss
      hxData.1 hyData.1 hxy
      (allActiveTranslatedFibreCoordinate
        C exponent word x)
  have hyWord :
      word ∈ translatedCompletionWords C y.1
        (allActiveTranslatedFibreCoordinate
          C exponent word x) := by
    simpa [hcoord] using hySpec.2
  exact Finset.disjoint_left.mp hdisj
    hxSpec.2 hyWord

theorem allActiveTranslatedLossFibre_card_le_n
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (word : Fin n → Bool) :
    (allActiveTranslatedLossFibre C exponent word).card ≤ n := by
  classical
  have hcard :=
    Fintype.card_le_of_injective
      (allActiveTranslatedFibreCoordinate C exponent word)
      (allActiveTranslatedFibreCoordinate_injective
        C exponent hexp honeLoss word)
  simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

#print axioms allActiveTranslatedFibreCoordinate_injective
#print axioms allActiveTranslatedLossFibre_card_le_n

end OrderedEdgeColoring
end JSP000404Research
