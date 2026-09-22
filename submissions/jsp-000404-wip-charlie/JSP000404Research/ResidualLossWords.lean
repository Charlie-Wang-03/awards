
import JSP000404Research.ResidualOverlapWitness
import JSP000404Research.WeightedOneLayerCharge
import Mathlib.Tactic

/-!
# Exact projected profile loss is a concrete disjoint Boolean-word set

Let

  Loss = {v | exponent(v) = projectedFree(v)+1}.

Under the standard one-layer residual projection hypothesis, every v in Loss
is residual-inactive.  Any nontrivial intersection of two retained completion
cubes forces their joining edge to be residual.  Therefore the completion cube
of a loss vertex is disjoint from every other vertex's completion cube.

Consequently the loss completion cubes are pairwise disjoint, and their union
has cardinality exactly

  sum_{v in Loss} 2^projectedFree(v)
    = totalDyadicProfileLoss(exponent, projectedFree).

Moreover no loss completion word can be an overlapCompletionWord.

Thus the two costs in ResidualProjectionAccounting,

  overlapMass + profileLoss,

are literally the cardinalities of two disjoint finite sets of retained
Boolean words.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

noncomputable def projectedLossVertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset V :=
  oneLayerLossVertices exponent (projectedFree C)

@[simp] theorem mem_projectedLossVertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (v : V) :
    v ∈ projectedLossVertices C exponent ↔
      exponent v = projectedFree C v + 1 := by
  simp [projectedLossVertices]

theorem residual_inactive_of_mem_projectedLossVertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V}
    (hv : v ∈ projectedLossVertices C exponent) :
    residualCoord n ∉ active C v := by
  have hexact :
      exponent v = projectedFree C v + 1 :=
    (mem_projectedLossVertices C exponent v).1 hv
  exact (exact_projected_loss_rigidity
    C exponent hexp honeLoss
    hexact rfl).1

/-- A projected-loss completion cube is disjoint from every other completion
cube. -/
theorem projectedLoss_completion_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hv : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w) :
    Disjoint
      (retainedCompletionWords C v)
      (retainedCompletionWords C w) := by
  classical
  rw [Finset.disjoint_left]
  intro word hvWord hwWord
  have hinactive :=
    residual_inactive_of_mem_projectedLossVertices
      C exponent hexp honeLoss hv
  rcases retainedCompletion_overlap_forces_residual
      C hvw hvWord hwWord with hres | hres
  · exact hinactive
      (residualCoord_mem_active_of_isResidual
        C hres.1 hres.2).1
  · exact hinactive
      (residualCoord_mem_active_of_isResidual
        C hres.1 hres.2).2

theorem projectedLoss_completion_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1) :
    ((projectedLossVertices C exponent : Finset V) : Set V).PairwiseDisjoint
      (retainedCompletionWords C) := by
  intro v hv w hw hvw
  exact projectedLoss_completion_disjoint
    C exponent hexp honeLoss hv hvw

noncomputable def lossCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Finset (Fin n → Bool) :=
  (projectedLossVertices C exponent).biUnion
    (retainedCompletionWords C)

@[simp] theorem mem_lossCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool) :
    word ∈ lossCompletionWords C exponent ↔
      ∃ v, v ∈ projectedLossVertices C exponent ∧
        word ∈ retainedCompletionWords C v := by
  classical
  simp [lossCompletionWords]

/-- The loss-word union has exactly the one-layer loss weight. -/
theorem lossCompletionWords_card_eq_oneLayerLossWeight
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (lossCompletionWords C exponent).card =
      oneLayerLossWeight exponent (projectedFree C) := by
  classical
  rw [lossCompletionWords,
      Finset.card_biUnion
        (projectedLoss_completion_pairwiseDisjoint
          C exponent hexp honeLoss)]
  rw [oneLayerLossWeight_eq_sum_lossVertices]
  apply Finset.sum_congr rfl
  intro v hv
  rw [retainedCompletionWords_card]
  rfl

/-- Under the one-layer profile bound, lossCompletionWords has cardinality
exactly the total dyadic profile loss. -/
theorem lossCompletionWords_card_eq_totalDyadicProfileLoss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (lossCompletionWords C exponent).card =
      totalDyadicProfileLoss exponent (projectedFree C) := by
  have honeProfile :=
    exponent_le_projectedFree_add_one
      C exponent hexp honeLoss
  rw [totalDyadicProfileLoss_eq_oneLayerLossWeight
      exponent (projectedFree C) honeProfile]
  exact lossCompletionWords_card_eq_oneLayerLossWeight
    C exponent hexp honeLoss

/-- Loss words and double-covered words are disjoint. -/
theorem lossCompletionWords_disjoint_overlapCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Disjoint
      (lossCompletionWords C exponent)
      (overlapCompletionWords C) := by
  classical
  rw [Finset.disjoint_left]
  intro word hLoss hOverlap
  obtain ⟨v, hvLoss, hvWord⟩ :=
    (mem_lossCompletionWords C exponent word).1 hLoss
  obtain ⟨u, w, huw, _hres, huWord, hwWord, huniq⟩ :=
    exists_ordered_residual_pair_of_overlapWord
      C hOverlap
  have hvEq := huniq v hvWord
  rcases hvEq with rfl | rfl
  · have hdisj :=
      projectedLoss_completion_disjoint
        C exponent hexp honeLoss hvLoss (ne_of_lt huw)
    exact Finset.disjoint_left.mp hdisj hvWord hwWord
  · have hdisj :=
      projectedLoss_completion_disjoint
        C exponent hexp honeLoss hvLoss (ne_of_lt huw).symm
    exact Finset.disjoint_left.mp hdisj hvWord huWord

/-- Therefore overlapMass + profileLoss is the cardinality of one concrete
finite bad-word set. -/
theorem badProjectionWords_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (lossCompletionWords C exponent ∪
      overlapCompletionWords C).card =
      totalDyadicProfileLoss exponent (projectedFree C) +
        (overlapCompletionWords C).card := by
  rw [Finset.card_union_of_disjoint
      (lossCompletionWords_disjoint_overlapCompletionWords
        C exponent hexp honeLoss),
      lossCompletionWords_card_eq_totalDyadicProfileLoss
        C exponent hexp honeLoss]
  omega

#print axioms residual_inactive_of_mem_projectedLossVertices
#print axioms projectedLoss_completion_disjoint
#print axioms lossCompletionWords_card_eq_totalDyadicProfileLoss
#print axioms lossCompletionWords_disjoint_overlapCompletionWords
#print axioms badProjectionWords_card

end OrderedEdgeColoring
end JSP000404Research
