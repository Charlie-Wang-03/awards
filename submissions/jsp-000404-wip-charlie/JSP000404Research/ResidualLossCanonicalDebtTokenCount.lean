import JSP000404Research.ResidualLossEarliestCollision
import JSP000404Research.ResidualLossCollisionThreePointExternalHoleObstruction
import Mathlib.Tactic

/-!
# Exact typed source tokens for the ACTUAL translated-loss duplicate debt

The previous arbitrary set of ordered (c,d,w) collision records does not
measure the real debt: the two orderings of a pair could count the same event
twice.  This file instead uses the existing exact first-prior coordinate
decomposition. For every later i, its earliest earlier j and word w form ONE
source token. The type's cardinal is exactly translatedLossDuplicateDebt.

This turns the previous anonymous Fin debt units into genuine original
word/coordinate certificates. Payment to real exterior holes still requires
an actual globally injective assignment. No new exterior hole is assumed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Actual duplicate-debt tokens: later i, earliest prior j < i, and a
Boolean word in the exact earliest-prior intersection component.
Unlike arbitrary (c,d,w) pairs, the flipped ordering is NOT a second token. -/
abbrev actualEarliestLossDebtTokenType
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) : Type _ :=
  Σ i : Fin n, Σ j : Fin i.val,
    {w : Fin n → Bool // w ∈ lossEarliestPairWords
      (lossSliceAtNat C exponent choice) i.val j.val}

/-- The typed source count is literally the ORIGINAL cross-coordinate
overcount. This removes coordinate-order double-charging without any
geometric or payment assumption. -/
theorem actual_earliest_loss_debt_tokens_card_eq_duplicate_debt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    Fintype.card (actualEarliestLossDebtTokenType C exponent choice) =
      translatedLossDuplicateDebt C exponent choice := by
  classical
  rw [translatedLossDuplicateDebt_eq_sum_earliestPairWords]
  simp only [actualEarliestLossDebtTokenType, Fintype.card_sigma,
    Fintype.card_coe]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_fin_eq_sum_range]
  rfl

/-- The candidate opposite Boolean corner of one *genuine exact debt*
token, with its earliest prior coordinate lifted back to Fin n. -/
noncomputable def actualEarliestLossDebtOppositeWord
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (x : actualEarliestLossDebtTokenType C exponent choice) :
    Fin n → Bool :=
  flipBoolWordAt
    (flipBoolWordAt x.2.2.1 x.1)
    ⟨x.2.1.val, lt_trans x.2.1.isLt x.1.isLt⟩

/-- A SOURCE-NATIVE sufficient certificate for paying the entire
ORIGINAL projected-loss duplicate debt in genuine, nonreused,
outside-translated Boolean holes. Both hypotheses are real geometric
questions: every chosen opposite word must truly be exterior, and
two distinct actual debt tokens cannot claim the same word.

This DOES NOT pay the other seven debt classes or settle the root sorry. -/
theorem actual_earliest_loss_duplicate_debt_paid_of_injective_real_opposites
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hreal : ∀ x : actualEarliestLossDebtTokenType C exponent choice,
      actualEarliestLossDebtOppositeWord C exponent choice x ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice)
    (hinjective : Function.Injective
      (actualEarliestLossDebtOppositeWord C exponent choice)) :
    translatedLossDuplicateDebt C exponent choice ≤
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card := by
  classical
  let allocation :
      actualEarliestLossDebtTokenType C exponent choice →
        {w : Fin n → Bool //
          w ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice} :=
    fun x => ⟨actualEarliestLossDebtOppositeWord C exponent choice x,
      hreal x⟩
  have halloc : Function.Injective allocation := by
    intro x y h
    exact hinjective (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective allocation halloc
  rw [actual_earliest_loss_debt_tokens_card_eq_duplicate_debt] at hcard
  simpa only [Fintype.card_coe] using hcard

#print axioms actual_earliest_loss_debt_tokens_card_eq_duplicate_debt
#print axioms actual_earliest_loss_duplicate_debt_paid_of_injective_real_opposites

end OrderedEdgeColoring
end JSP000404Research
