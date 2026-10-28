import JSP000404Research.ActualOneLossCentreNonlocalBudget
import JSP000404Research.ResidualLossActualEdgeCarrierFrontier
import Mathlib.Tactic

/-!
# Two genuine ledger lanes eliminated when NO projected loss centre exists

No source of a chosen active-loss/blocker edge can exist when the original
projected loss set is empty. The original covered-blocker class then vanishes.
The separately certified no-earliest-prior-collision lemma eliminates the
eighth duplicate-debt class under the same hypothesis.

This gives an *exact* reduction to the remaining six original terminal classes
for arbitrary n and arbitrary finite original V; no external true hole or
unreserved surplus is invented. It is NOT an unconditional capacity theorem
and does not discharge the remaining original root admission.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A real source-to-blocker carrier requires a genuine original
projected-loss source. The exact chosen/actual edge-filter is empty if
the original projected-loss vertex set is empty. -/
theorem actual_zero_loss_centres_no_chosen_edge_blockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hloss0 : (projectedLossVertices C exponent).card = 0) :
    chosenLossActualEdgeBlockerTriples C exponent choice = ∅ := by
  classical
  have hnone : projectedLossVertices C exponent = ∅ :=
    Finset.card_eq_zero.mp hloss0
  ext z
  simp [chosenLossActualEdgeBlockerTriples,
    chosenLossCoveredBlockerTriples, hnone]

/-- With no original projected-loss vertex, the actual eight-source
numerical payment inequality reduces EXACTLY to the six-class terminal
dyadic debt inequality: both the genuine chosen covered-blocker union
and the literal eighth original collision-debt count are zero.

The six-class terminal inequality remains a mathematical obligation. -/
theorem actual_zero_loss_centres_payment_iff_six_terminal_sources
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hloss0 : (projectedLossVertices C exponent).card = 0) :
    (terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        translatedLossDuplicateDebt C exponent choice ≤
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
        terminalTwinAvailableSurplus C exponent) ↔
    (terminalTwinOtherFiveDebt C exponent ≤
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
        terminalTwinAvailableSurplus C exponent) := by
  have hloss1 : (projectedLossVertices C exponent).card ≤ 1 := by omega
  have hdup :=
    actual_original_at_most_one_loss_centre_no_eighth_debt
      C exponent choice hloss1
  have hblock :=
    actual_zero_loss_centres_no_chosen_edge_blockers
      C exponent choice hloss0
  simp only [hdup, hblock, Finset.biUnion_empty,
    Finset.card_empty, Nat.add_zero]

#print axioms actual_zero_loss_centres_no_chosen_edge_blockers
#print axioms actual_zero_loss_centres_payment_iff_six_terminal_sources

end OrderedEdgeColoring
end JSP000404Research
