import JSP000404Research.ResidualLossCollisionSharedCornerHallObstruction
import JSP000404Research.ResidualLossCanonicalDebtTokenCount
import Mathlib.Tactic

/-!
# Certified bijection: genuine earliest-prior collision records = actual duplicate-debt units

There were two independently verified descriptions of real translated-loss
duplicates: the source-native dependent Sigma type and the set of
earliest-prior collision triples. This module proves they are EQUIVALENT,
with no coordinate-order double counting. It then connects the earlier
local true-hole Hall obstruction to the LITERAL original debt quantity.

This is only a necessary/local resource obstruction, NOT a global
nonreusing payment or a proof of the planar capacity theorem.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Convert a real dependent (later, prior, word) debt unit into an
ordinary triple, forgetting only proof witnesses (never source data). -/
noncomputable def actualEarliestLossDebtRecord
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (x : actualEarliestLossDebtTokenType C exponent choice) :
    Fin n × Fin n × (Fin n → Bool) :=
  (x.1, ⟨x.2.1.val, lt_trans x.2.1.isLt x.1.isLt⟩, x.2.2.1)

/-- Every dependent debt unit is an ORIGINAL earliest-prior source,
rather than an artificial ordered pair. -/
theorem actual_earliest_loss_debt_record_mem
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (x : actualEarliestLossDebtTokenType C exponent choice) :
    actualEarliestLossDebtRecord C exponent choice x ∈
      actualEarliestLossCollisionRecords C exponent choice := by
  classical
  change (actualEarliestLossDebtRecord C exponent choice x) ∈
    (Finset.univ : Finset (Fin n × Fin n × (Fin n → Bool))).filter
      (fun a => a.2.1 < a.1 ∧
        a.2.2 ∈ lossEarliestPairWords
          (lossSliceAtNat C exponent choice) a.1.val a.2.1.val)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x.2.1.isLt, x.2.2.2⟩

/-- Exact source-level equivalence: one token for each earliest-prior
record, with NO duplicate for reversing the two coordinates. -/
noncomputable def actualEarliestLossDebtEquivCollisionRecord
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    actualEarliestLossDebtTokenType C exponent choice ≃
      {a : Fin n × Fin n × (Fin n → Bool) //
        a ∈ actualEarliestLossCollisionRecords C exponent choice} where
  toFun := fun x => ⟨actualEarliestLossDebtRecord C exponent choice x,
    actual_earliest_loss_debt_record_mem C exponent choice x⟩
  invFun := fun a =>
    let ha := (Finset.mem_filter.mp a.2).2
    ⟨a.1.1, ⟨⟨a.1.2.1.val, ha.1⟩, ⟨a.1.2.2, ha.2⟩⟩⟩
  left_inv := by
    intro x
    rcases x with ⟨i, j, w⟩
    rfl
  right_inv := by
    intro a
    rcases a with ⟨⟨i, j, w⟩, ha⟩
    apply Subtype.ext
    rfl

/-- Exact canonical collision RECORD COUNT = the unmodified original
translated-loss duplicate-debt integer. No Hall or AngleCap hypothesis. -/
theorem actual_earliest_collision_records_card_eq_duplicate_debt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    (actualEarliestLossCollisionRecords C exponent choice).card =
      translatedLossDuplicateDebt C exponent choice := by
  classical
  have hcard := Fintype.card_congr
    (actualEarliestLossDebtEquivCollisionRecord C exponent choice)
  rw [actual_earliest_loss_debt_tokens_card_eq_duplicate_debt] at hcard
  simpa only [Fintype.card_coe] using hcard.symm

/-- Directly ORIGINAL-DEBT-VALUED local Hall obstruction:
if the distinct opposite true-hole CANDIDATES of the genuine earliest
collision records are fewer than the actual duplicate debt, then the
TRUE hole neighbourhood *inside the source collision squares* cannot
pay this original debt. This does NOT exclude NONLOCAL holes or surplus. -/
theorem actual_duplicate_debt_local_hall_shortfall_of_opposite_reuse
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hshort :
      ((actualEarliestLossCollisionRecords C exponent choice).image
        (fun a =>
          flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)).card <
        translatedLossDuplicateDebt C exponent choice) :
    ¬ translatedLossDuplicateDebt C exponent choice ≤
      ((actualEarliestLossCollisionRecords C exponent choice).biUnion
        (fun a =>
          lossCollisionSquareWords n a ∩
            lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card := by
  have hcard :=
    actual_earliest_collision_records_card_eq_duplicate_debt
      C exponent choice
  rw [← hcard] at hshort ⊢
  exact actual_earliest_loss_collision_local_hall_shortfall_of_reused_corner
    C exponent choice hshort

#print axioms actual_earliest_loss_debt_record_mem
#print axioms actual_earliest_collision_records_card_eq_duplicate_debt
#print axioms actual_duplicate_debt_local_hall_shortfall_of_opposite_reuse

end OrderedEdgeColoring
end JSP000404Research
