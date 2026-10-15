import JSP000404Research.ResidualLossExternalHoleBudget
import JSP000404Research.ResidualTerminalTwinNetPaymentReduction
import Mathlib.Tactic

/-!
# The exact six-source frontier with the projected-loss term eliminated

The old global inequality has five other debt classes plus
`totalDyadicProfileLoss`, paid by global true Boolean holes and
unreserved dyadic surplus. We rewrite it *without altering any term*:

  six-source inequality
    iff
  other five debts + covered translated-loss blockers
                   + cross-coordinate duplicate debt
      <= TRUE holes outside ALL translated-loss slices
                   + genuinely unreserved surplus.

This is a logically equivalent obstruction frontier; in particular,
it does not assume the right-hand side is large enough.
The remaining geometry is NOT discharged.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Global available true holes equal all Boolean words minus those
covered by at least one original retained completion cube. -/
theorem lossLedgerGlobalTrueHoles_card_eq_two_pow_sub_covered
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (lossLedgerGlobalTrueHoles C).card =
      2 ^ n - (coveredCompletionWords C).card := by
  classical
  let K : Finset (Fin n → Bool) := coveredCompletionWords C
  let H : Finset (Fin n → Bool) := lossLedgerGlobalTrueHoles C
  have hpartition :
      (Finset.univ : Finset (Fin n → Bool)) = H ∪ K := by
    ext word
    simp [H, K, lossLedgerGlobalTrueHoles]
  have hdisjoint : Disjoint H K := by
    apply Finset.disjoint_left.mpr
    intro word hH hK
    change word ∈ (Finset.univ : Finset (Fin n → Bool)) \ K at hH
    exact (Finset.mem_sdiff.mp hH).2 hK
  have hUniv : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp
  have hmass : 2 ^ n = H.card + K.card := by
    calc
      2 ^ n = (Finset.univ : Finset (Fin n → Bool)).card := hUniv.symm
      _ = (H ∪ K).card := congrArg Finset.card hpartition
      _ = H.card + K.card := Finset.card_union_of_disjoint hdisjoint
  change H.card = 2 ^ n - K.card
  omega

/-- The genuine five remaining six-source debt classes, each counted
in the same term and order as the verified terminal-twin reduction. -/
noncomputable def terminalTwinOtherFiveDebt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : ℕ :=
  (softOverlapCompletionWords C).card +
    (netTransportableHardWords C exponent).card +
    (netStrictDescentRigidWords C exponent).card +
    (∑ q ∈ netTwinRigidCarriers C exponent, 2 ^ exponent q.2) +
    (∑ q ∈ ascendingUnpaidRigidCarriers C exponent,
      2 ^ exponent q.1) +
    (∑ q ∈ descendingUnpaidRigidCarriers C exponent,
      2 ^ exponent q.2)

/-- The unchanged one-layer surplus minus *all* pre-reserved credits
of the old terminal-twin payment interface. -/
noncomputable def terminalTwinAvailableSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : ℕ :=
  totalDyadicProfileSurplus exponent (projectedFree C) -
    (surplusPaidHardOverlapWords C exponent).card -
    (∑ q ∈ ascendingUnpaidRigidCarriers C exponent,
      dyadicProfileSurplus exponent (projectedFree C) q.1) -
    (∑ q ∈ descendingUnpaidRigidCarriers C exponent,
      dyadicProfileSurplus exponent (projectedFree C) q.2)

/-- Exact bidirectional rewrite of the *actual* six-source terminal
payment. No extra assumption on the geometry or either budget. -/
theorem terminalTwinSixSourcePayment_iff_externalLossObstruction
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    (terminalTwinOtherFiveDebt C exponent +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
      (2 ^ n - (coveredCompletionWords C).card) +
      terminalTwinAvailableSurplus C exponent) ↔
    (terminalTwinOtherFiveDebt C exponent +
      (translatedLossCoveredWords C exponent choice).card +
      translatedLossDuplicateDebt C exponent choice ≤
      (lossLedgerOutsideTranslatedTrueHoles
        C exponent choice).card +
      terminalTwinAvailableSurplus C exponent) := by
  have h := lossProfilePayment_iff_externalTrueHolePayment
    C exponent hexp honeLoss choice
    (terminalTwinOtherFiveDebt C exponent)
    (terminalTwinAvailableSurplus C exponent)
  rw [lossLedgerGlobalTrueHoles_card_eq_two_pow_sub_covered C] at h
  exact h

#print axioms lossLedgerGlobalTrueHoles_card_eq_two_pow_sub_covered
#print axioms terminalTwinSixSourcePayment_iff_externalLossObstruction

end OrderedEdgeColoring
end JSP000404Research
