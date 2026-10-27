import JSP000404Research.ActualEightSourceCriticalHallCore
import JSP000404Research.ActualEightSourceEarliestHallBridge
import Mathlib.Tactic

/-!
# Hall eligibility quantifier audit: arbitrary eligibility is no geometric gain

A true source-specific Hall expansion must use a geometrically grounded
eligibility relation (true exterior holes and genuinely unreserved surplus
tokens that an individual actual debt source can legally claim).

If eligibility may be ANY function of source tokens into the set of the
two existing legal credit types, then choosing the WHOLE credit Finset
at EVERY source shows:

    EXISTS eligible satisfying every finite Hall inequality
        IFF
    number of actual eight-lane debt tokens <= number of real credits.

Thus existentially quantifying an unconstrained eligibility relation
is ONLY the original numerical payment requirement restated; it
provides no independent planar/geometric lemma. This audit is intended
to rule out a falsely claimed discharge of the global JSP-000404 sorry.

The actual total source family includes genuine earliest-prior duplicate
records and all seven other source classes. The credit family is literally
the existing true-exterior-hole / genuinely unreserved surplus sum type.
The argument creates NO extra credits, does NOT assert numerical payment,
and does NOT discharge the remaining root sorry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A complete finite bipartite eligibility relation satisfies all Hall
inequalities exactly when the TOTAL source cardinality is bounded by
the TOTAL credit cardinality. In particular allowing arbitrary
eligibility makes Hall no more than a counting inequality. -/
theorem complete_finite_eligibility_hall_iff_card_le
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] :
    (∀ S : Finset α,
      S.card ≤ (S.biUnion
        (fun _ => (Finset.univ : Finset β))).card) ↔
      Fintype.card α ≤ Fintype.card β := by
  classical
  constructor
  · intro hHall
    by_cases hNonempty : (Finset.univ : Finset α).Nonempty
    · obtain ⟨a, ha⟩ := hNonempty
      have hUnion :
          ((Finset.univ : Finset α).biUnion
            (fun _ => (Finset.univ : Finset β))) =
            (Finset.univ : Finset β) := by
        ext b
        constructor
        · intro _
          exact Finset.mem_univ b
        · intro _
          exact Finset.mem_biUnion.mpr
            ⟨a, ha, Finset.mem_univ b⟩
      have hMain := hHall (Finset.univ : Finset α)
      simpa only [Finset.card_univ, hUnion] using hMain
    · have hEmpty : (Finset.univ : Finset α) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hNonempty
      have hZero : Fintype.card α = 0 := by
        have hc := congrArg Finset.card hEmpty
        simpa using hc
      omega
  · intro hCard S
    by_cases hS : S.Nonempty
    · obtain ⟨a, ha⟩ := hS
      have hUnion :
          (S.biUnion (fun _ => (Finset.univ : Finset β))) =
            (Finset.univ : Finset β) := by
        ext b
        constructor
        · intro _
          exact Finset.mem_univ b
        · intro _
          exact Finset.mem_biUnion.mpr
            ⟨a, ha, Finset.mem_univ b⟩
      rw [hUnion]
      exact (Finset.card_le_card (Finset.subset_univ S)).trans hCard
    · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [hEmpty]

/-- An UNCONSTRAINED existential eligibility relation on the authentic
eight-lane earliest-collision source type is exactly equivalent to the
ORIGINAL unchanged global numerical payment inequality.

This theorem diagnoses a precise semantic hard stop: an argument that
merely invents some eligible source-to-credit relation with Hall
expansion cannot prove more than the original capacity obligation.
A useful eligibility relation must be constrained by additional,
independently established, source-specific geometric facts. -/
theorem actual_eight_earliest_arbitrary_eligibility_hall_iff_payment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n) :
    (∃ eligible :
      actualEightSourceEarliestDebtTokens B k choice →
        Finset (actualExternalPaymentCredits B k choice),
        ∀ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
          S.card ≤ (S.biUnion eligible).card) ↔
    terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        translatedLossDuplicateDebt B k choice ≤
      (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
        terminalTwinAvailableSurplus B k := by
  classical
  constructor
  · rintro ⟨eligible, hHall⟩
    exact actual_eight_source_earliest_hall_implies_global_payment
      B k choice eligible hHall
  · intro hPayment
    have hCount :
        Fintype.card (actualEightSourceEarliestDebtTokens B k choice) ≤
          Fintype.card (actualExternalPaymentCredits B k choice) := by
      simpa only [actualEightSourceEarliestDebtTokens,
        actualExternalPaymentCredits, terminalTwinOtherFiveDebt,
        Fintype.card_sum, Fintype.card_fin, Fintype.card_coe,
        actual_earliest_loss_debt_tokens_card_eq_duplicate_debt,
        Nat.add_assoc] using hPayment
    refine ⟨(fun _ => Finset.univ), ?_⟩
    exact (complete_finite_eligibility_hall_iff_card_le).mpr hCount

#print axioms complete_finite_eligibility_hall_iff_card_le
#print axioms actual_eight_earliest_arbitrary_eligibility_hall_iff_payment

end OrderedEdgeColoring
end JSP000404Research
