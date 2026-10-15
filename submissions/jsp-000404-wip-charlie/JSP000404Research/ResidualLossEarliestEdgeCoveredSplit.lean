import JSP000404Research.ResidualLossEarliestEdgeThirdPartyCover
import JSP000404Research.ResidualLossEarliestActualEdgeGlobalLedger
import Mathlib.Tactic

/-!
# Exact covered-versus-uncovered split of real-edge collision debt

The exact (later coordinate, earliest predecessor, actual edge pair)
duplicate debt can be decomposed by whether its collision Boolean word
is in the ORIGINAL covered completion union K.

Ddup = Ddup_covered + Ddup_trueHole.

When flip choices are active, a carrier word is covered precisely
when a THIRD original vertex owns it. A carrier true-hole word is
still inside translated-loss U, not available as an outside-U hole.
This formal identity does not pay either part globally.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Actual edge-local duplicate mass whose collision word is itself
already covered by some ORIGINAL completion cube. -/
noncomputable def lossEarliestEdgeCoveredMassAtNat
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (i j : ℕ) : ℕ :=
  if hi : i < n then
    if hj : j < n then
      ∑ p ∈ crossLossConflictPairs C exponent choice
          ⟨i, hi⟩ ⟨j, hj⟩,
        (lossEarliestActualEdgeCarrier C exponent choice
          ⟨i, hi⟩ ⟨j, hj⟩ p ∩
            coveredCompletionWords C).card
    else 0
  else 0

/-- Actual edge-local duplicate mass whose collision word lies
outside the ORIGINAL covered completion union; these words are
global true holes but still lie inside translated-loss U. -/
noncomputable def lossEarliestEdgeTrueHoleMassAtNat
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (i j : ℕ) : ℕ :=
  if hi : i < n then
    if hj : j < n then
      ∑ p ∈ crossLossConflictPairs C exponent choice
          ⟨i, hi⟩ ⟨j, hj⟩,
        (lossEarliestActualEdgeCarrier C exponent choice
          ⟨i, hi⟩ ⟨j, hj⟩ p \
            coveredCompletionWords C).card
    else 0
  else 0

/-- Exact finite mass conservation at a fixed pair of natural
coordinate indices: covered collision events plus uncovered
collision events equal all actual edge collision events. -/
theorem lossEarliestActualEdgeMassAtNat_eq_covered_add_trueHole
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (i j : ℕ) :
    lossEarliestActualEdgeMassAtNat C exponent choice i j =
      lossEarliestEdgeCoveredMassAtNat C exponent choice i j +
        lossEarliestEdgeTrueHoleMassAtNat C exponent choice i j := by
  classical
  unfold lossEarliestActualEdgeMassAtNat
    lossEarliestEdgeCoveredMassAtNat
    lossEarliestEdgeTrueHoleMassAtNat
  split_ifs with hi hj
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpart :=
      Finset.card_sdiff_add_card_inter
        (lossEarliestActualEdgeCarrier C exponent choice
          ⟨i, hi⟩ ⟨j, hj⟩ p)
        (coveredCompletionWords C)
    omega
  all_goals simp

/-- Global exact duplicate-debt conservation: every actual source/
blocker event is charged ONCE to either a covered collision word or
a globally uncovered collision word, with all later-coordinate
multiplicities retained. No outside true holes are generated. -/
theorem translatedLossDuplicateDebt_eq_covered_plus_trueHole_edge_mass
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice =
      (∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range i,
          lossEarliestEdgeCoveredMassAtNat
            C exponent choice i j) +
      (∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range i,
          lossEarliestEdgeTrueHoleMassAtNat
            C exponent choice i j) := by
  classical
  calc
    translatedLossDuplicateDebt C exponent choice =
        ∑ i ∈ Finset.range n,
          ∑ j ∈ Finset.range i,
            (lossEarliestEdgeCoveredMassAtNat C exponent choice i j +
              lossEarliestEdgeTrueHoleMassAtNat C exponent choice i j) := by
      rw [translatedLossDuplicateDebt_eq_sum_earliest_actual_edges
        C exponent hexp honeLoss choice]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact lossEarliestActualEdgeMassAtNat_eq_covered_add_trueHole
        C exponent choice i j
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]

#print axioms lossEarliestActualEdgeMassAtNat_eq_covered_add_trueHole
#print axioms translatedLossDuplicateDebt_eq_covered_plus_trueHole_edge_mass

end OrderedEdgeColoring
end JSP000404Research
