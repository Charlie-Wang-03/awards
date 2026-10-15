import JSP000404Research.ResidualTerminalTwinExternalHoleFrontier
import JSP000404Research.ResidualLossActiveFlipBlocker
import Mathlib.Tactic

/-!
# Six-source payment iff there exists a genuinely active flip allocation

The previous exact external-hole frontier held for **any** flip-choice
function. An arbitrary choice may waste mass by flipping an inactive
coordinate and leaving a loss word in its own original completion cube.

For n>=1 and k(v)<=n, every projected-loss vertex provably has at least
one retained-active coordinate. Therefore the original six-source payment
is equivalent to the **existence** of an active loss choice satisfying the
external-hole frontier.

Any covered translated word of such a choice has a *distinct* blocker
centre, with the chosen coordinate active at both centres, as certified
by ResidualLossActiveFlipBlocker. Hence the residual covered-debt term
now has an actual two-owner structural witness.

No new geometric hypothesis is imposed on the original theorem. This
proves a strict refinement of the exact obstruction *interface*, not
the outstanding global inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem terminalTwinSixSourcePayment_iff_exists_active_externalFrontier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : 1 ≤ n) :
    (terminalTwinOtherFiveDebt C exponent +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
      (2 ^ n - (coveredCompletionWords C).card) +
      terminalTwinAvailableSurplus C exponent) ↔
    ∃ choice : V → Fin n,
      (∀ v ∈ projectedLossVertices C exponent,
        choice v ∈ retainedActive C v) ∧
      (terminalTwinOtherFiveDebt C exponent +
        (translatedLossCoveredWords C exponent choice).card +
        translatedLossDuplicateDebt C exponent choice ≤
        (lossLedgerOutsideTranslatedTrueHoles
          C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) := by
  constructor
  · intro hpayment
    let choice : V → Fin n :=
      projectedLossActiveFlipChoice C exponent hexp hn
    refine ⟨choice, ?_, ?_⟩
    · intro v hv
      exact projectedLossActiveFlipChoice_mem_retainedActive
        C exponent hexp hn hv
    · exact (terminalTwinSixSourcePayment_iff_externalLossObstruction
        C exponent hexp honeLoss choice).1 hpayment
  · rintro ⟨choice, _hactive, hpayment⟩
    exact (terminalTwinSixSourcePayment_iff_externalLossObstruction
      C exponent hexp honeLoss choice).2 hpayment

#print axioms terminalTwinSixSourcePayment_iff_exists_active_externalFrontier

end OrderedEdgeColoring
end JSP000404Research
