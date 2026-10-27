import JSP000404Research.PlanarActualEarliestEightSourceHallFrontier
import Mathlib.Tactic

/-!
# One-credit deficit reduction for the REAL eight-source Hall frontier

An arbitrary failed finite Hall expansion has a genuinely smaller
obstruction whose deficit is EXACTLY ONE: a source subset T with

  |N(T)| + 1 = |T|.

This follows by deleting a source as long as the remaining family is
still deficient. The first source family that cannot be further
reduced has exactly a one-credit deficiency, because adding one
source cannot reduce its set of eligible genuine credits.

Consequently, to prove Hall expansion for the ACTUAL eight SOURCE-
TAGGED debt tokens into the TWO REAL credit classes, it suffices to
exclude ONLY these unit-deficit finite families. No anonymous tokens
are introduced, no credit is manufactured, and no unrelated
geometric hypotheses are substituted for AngleCap.

The geometric nonexistence of unit-deficit original-source families
under AngleCap is NOT established here. This theorem is an
unconditional combinatorial strengthening of the exact open
payment obligation, NOT discharge of the single global root sorry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A finite Hall deficiency of arbitrary magnitude always contains
a (possibly smaller) source family with a deficit of exactly one.
Unlike a cardinal bound on the entire source set, this provides a
precisely localized non-reusing shortage witness. -/
theorem finite_hall_failure_contains_unit_deficit
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (eligible : α → Finset β)
    (S : Finset α)
    (hbad : (S.biUnion eligible).card < S.card) :
    ∃ T : Finset α, T ⊆ S ∧
      (T.biUnion eligible).card + 1 = T.card := by
  induction S using Finset.induction_on with
  | empty =>
      simp at hbad
  | @insert a S ha ih =>
      by_cases hsmaller : (S.biUnion eligible).card < S.card
      · obtain ⟨T, hT, hUnit⟩ := ih hsmaller
        exact ⟨T, hT.trans (Finset.subset_insert a S), hUnit⟩
      · have hHallSmall : S.card ≤ (S.biUnion eligible).card :=
          Nat.le_of_not_gt hsmaller
        have hsubset :
            S.biUnion eligible ⊆
              (insert a S).biUnion eligible := by
          intro b hb
          obtain ⟨i, hi, hbi⟩ := Finset.mem_biUnion.mp hb
          exact Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_insert_of_mem hi, hbi⟩
        have hmono := Finset.card_le_card hsubset
        have hcard : (insert a S).card = S.card + 1 :=
          Finset.card_insert_of_not_mem ha
        refine ⟨insert a S, Finset.Subset.rfl, ?_⟩
        omega

/-- Quantified Hall expansion is EXACTLY equivalent to the
nonexistence of a one-credit deficit finite family.
All source and credit sets remain the actual eligible sets. -/
theorem finite_hall_iff_no_unit_deficit
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (eligible : α → Finset β) :
    (∀ S : Finset α, S.card ≤ (S.biUnion eligible).card) ↔
      (¬ ∃ S : Finset α,
        (S.biUnion eligible).card + 1 = S.card) := by
  constructor
  · intro hHall ⟨S, hUnit⟩
    have h := hHall S
    omega
  · intro hNoUnit S
    by_contra hNot
    have hbad : (S.biUnion eligible).card < S.card := by omega
    obtain ⟨T, _hsubset, hUnit⟩ :=
      finite_hall_failure_contains_unit_deficit eligible S hbad
    exact hNoUnit ⟨T, hUnit⟩

/-- The ACTUAL eight-source, earliest-prior duplicate record family
has the same one-unit-deficit equivalence, with ALL eight original
debt classes and ONLY genuine exterior-hole/unreserved credits. -/
theorem actual_eight_earliest_hall_iff_no_unit_deficit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (eligible :
      actualEightSourceEarliestDebtTokens B k choice →
        Finset (actualExternalPaymentCredits B k choice)) :
    (∀ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
      S.card ≤ (S.biUnion eligible).card) ↔
      (¬ ∃ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
        (S.biUnion eligible).card + 1 = S.card) := by
  classical
  exact finite_hall_iff_no_unit_deficit eligible

/-- Direct original eight-debt payoff of the exact unit-deficit
exclusion. This supplies a sharper finite geometric target:
to pay the true eight-source ledger, rule out a ONE-CREDIT deficit
in each real eligible neighbourhood, rather than quantify arbitrary
deficit magnitudes. The exclusion remains an EXPLICIT premise. -/
theorem actual_eight_earliest_no_unit_deficit_implies_payment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (eligible :
      actualEightSourceEarliestDebtTokens B k choice →
        Finset (actualExternalPaymentCredits B k choice))
    (hNoUnit :
      ¬ ∃ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
        (S.biUnion eligible).card + 1 = S.card) :
    terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        translatedLossDuplicateDebt B k choice ≤
      (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
        terminalTwinAvailableSurplus B k := by
  have hHall :=
    (actual_eight_earliest_hall_iff_no_unit_deficit
      B k choice eligible).mpr hNoUnit
  exact actual_eight_source_earliest_hall_implies_global_payment
    B k choice eligible hHall

#print axioms finite_hall_failure_contains_unit_deficit
#print axioms finite_hall_iff_no_unit_deficit
#print axioms actual_eight_earliest_hall_iff_no_unit_deficit
#print axioms actual_eight_earliest_no_unit_deficit_implies_payment

end OrderedEdgeColoring
end JSP000404Research
