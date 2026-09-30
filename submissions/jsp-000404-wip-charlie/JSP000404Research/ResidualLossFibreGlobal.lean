import JSP000404Research.ResidualLossFibreRigidity
import Mathlib.Tactic

/-!
# Global structure of one translated-loss fibre

Fix a Boolean word y and a chosen flip coordinate choice(v) for every vertex.
Define the translated-loss fibre to consist of projected-loss vertices whose
translated completion block contains y.

Two rigidity properties hold.

1. Coordinate injectivity:
   two distinct fibre vertices cannot use the same chosen coordinate, because
   equal-coordinate translated loss blocks are disjoint.  Hence the fibre has
   cardinality at most n.

2. Monotone owner bits:
   assuming every chosen coordinate is retained-active at its fibre vertex,
   if v<w and y(choice v)=false, then y(choice w)=false.  Equivalently the
   true-labelled fibre vertices form an initial segment and the false-labelled
   vertices form a final segment.

This is the finite global form of the pairwise fibre rigidity theorem.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def translatedLossFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (word : Fin n → Bool) : Finset V := by
  classical
  exact (projectedLossVertices C exponent).filter
    (fun v => word ∈ translatedCompletionWords C v (choice v))

@[simp] theorem mem_translatedLossFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (v : V) :
    v ∈ translatedLossFibre C exponent choice word ↔
      v ∈ projectedLossVertices C exponent ∧
      word ∈ translatedCompletionWords C v (choice v) := by
  classical
  simp [translatedLossFibre]

theorem translatedLossFibre_choice_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool) :
    Set.InjOn choice
      (translatedLossFibre C exponent choice word : Set V) := by
  intro v hv w hw hchoice
  have hvData :=
    (mem_translatedLossFibre
      C exponent choice word v).1 hv
  have hwData :=
    (mem_translatedLossFibre
      C exponent choice word w).1 hw
  by_contra hvw
  have hdisj :=
    translated_loss_blocks_disjoint_same_coordinate
      C exponent hexp honeLoss
      hvData.1 hwData.1 hvw (choice v)
  have hwWord' :
      word ∈ translatedCompletionWords C w (choice v) := by
    simpa [hchoice] using hwData.2
  exact Finset.disjoint_left.mp hdisj
    hvData.2 hwWord'

theorem translatedLossFibre_card_le_n
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool) :
    (translatedLossFibre C exponent choice word).card ≤ n := by
  classical
  have hinj :=
    translatedLossFibre_choice_injective
      C exponent hexp honeLoss choice word
  have hcard :
      (translatedLossFibre C exponent choice word).card ≤
        Fintype.card (Fin n) := by
    exact Finset.card_le_card_of_injOn
      (fun v => choice v)
      (translatedLossFibre C exponent choice word)
      Finset.univ
      (fun v hv => Finset.mem_univ _)
      hinj
  simpa using hcard

theorem translatedLossFibre_false_propagates_right
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ v,
        v ∈ translatedLossFibre C exponent choice word →
        choice v ∈ retainedActive C v)
    {v w : V}
    (hv : v ∈ translatedLossFibre C exponent choice word)
    (hw : w ∈ translatedLossFibre C exponent choice word)
    (hvw : v < w)
    (hvFalse : word (choice v) = false) :
    word (choice w) = false := by
  have hvData :=
    (mem_translatedLossFibre
      C exponent choice word v).1 hv
  have hwData :=
    (mem_translatedLossFibre
      C exponent choice word w).1 hw
  exact translated_loss_fibre_monotone_bits
    C exponent hexp honeLoss
    hvw hvData.1 hwData.1
    (hactive v hv) (hactive w hw)
    hvData.2 hwData.2 hvFalse

theorem translatedLossFibre_true_propagates_left
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ v,
        v ∈ translatedLossFibre C exponent choice word →
        choice v ∈ retainedActive C v)
    {v w : V}
    (hv : v ∈ translatedLossFibre C exponent choice word)
    (hw : w ∈ translatedLossFibre C exponent choice word)
    (hvw : v < w)
    (hwTrue : word (choice w) = true) :
    word (choice v) = true := by
  cases h : word (choice v) with
  | false =>
      have hwFalse :=
        translatedLossFibre_false_propagates_right
          C exponent hexp honeLoss choice word hactive
          hv hw hvw h
      rw [hwTrue] at hwFalse
      contradiction
  | true =>
      exact h

#print axioms translatedLossFibre_choice_injective
#print axioms translatedLossFibre_card_le_n
#print axioms translatedLossFibre_false_propagates_right
#print axioms translatedLossFibre_true_propagates_left

end OrderedEdgeColoring
end JSP000404Research
