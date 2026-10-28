import JSP000404Research.ResidualLossCanonicalRecordDebtEquiv
import JSP000404Research.BooleanFlipCore
import Mathlib.Tactic

/-!
# The genuinely two-colour duplicate-debt source has NO repeated opposite target

The exact earliest-prior coordinate ordering j<i has only ONE possible
coordinate pair when n=2: i=1,j=0. Thus the opposite double-flip
map is injective on actual debt records, by the already proved
injectivity of Boolean coordinate flips.

This removes the entire *candidate reuse* source of the previous
local Hall shortfall in n=2, without claiming that any candidate is
a TRUE exterior hole. For n>=3 distinct coordinate pairs may compete
for one opposite word, and the global eight-source payment is OPEN.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- When n=1 there cannot be two distinct coordinate loss slices:
the original exact translated-loss duplicate debt is ZERO. -/
theorem actual_loss_duplicate_debt_zero_of_one_colour
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (1 + 1))
    (exponent : V → ℕ) (choice : V → Fin 1) :
    translatedLossDuplicateDebt C exponent choice = 0 := by
  by_contra hzero
  obtain ⟨c, d, hcd, _word, _hc, _hd⟩ :=
    positive_loss_duplicateDebt_has_slice_collision
      C exponent choice (Nat.pos_of_ne_zero hzero)
  exact hcd (Subsingleton.elim c d)

/-- The canonical (later, earlier) coordinate pair for a genuine
two-colour duplicate-debt record is necessarily (1,0). -/
theorem actual_earliest_loss_two_colour_record_only_pair
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (2 + 1))
    (exponent : V → ℕ) (choice : V → Fin 2)
    (a : Fin 2 × Fin 2 × (Fin 2 → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice) :
    a.1 = (1 : Fin 2) ∧ a.2.1 = (0 : Fin 2) := by
  have horder :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice a ha).2.1
  constructor
  · apply Fin.ext
    have ha' := a.1.isLt
    have hj' := a.2.1.isLt
    omega
  · apply Fin.ext
    have ha' := a.1.isLt
    have hj' := a.2.1.isLt
    omega

/-- In TWO Boolean colours no two DISTINCT true earliest-prior loss
collision records can ever share their opposite double-flip candidate.
This is unconditional: the opposite candidate may still be COVERED,
or lie inside translated loss, and therefore is NOT asserted to be
a usable exterior true hole. -/
theorem actual_two_colour_earliest_loss_opposite_injOn
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (2 + 1))
    (exponent : V → ℕ) (choice : V → Fin 2) :
    Set.InjOn
      (fun a : Fin 2 × Fin 2 × (Fin 2 → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)
      (actualEarliestLossCollisionRecords C exponent choice) := by
  intro a ha b hb heq
  have ha' := actual_earliest_loss_two_colour_record_only_pair
    C exponent choice a ha
  have hb' := actual_earliest_loss_two_colour_record_only_pair
    C exponent choice b hb
  have hword : a.2.2 = b.2.2 := by
    change flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
      flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1 at heq
    rw [ha'.1, ha'.2, hb'.1, hb'.2] at heq
    exact (flipBoolWordAt_injective (1 : Fin 2))
      ((flipBoolWordAt_injective (0 : Fin 2)) heq)
  apply Prod.ext
  · exact ha'.1.trans hb'.1.symm
  · apply Prod.ext
    · exact ha'.2.trans hb'.2.symm
    · exact hword

/-- A source-native sharp two-colour cardinal identity:
each ACTUAL duplicate-debt unit has its own distinct opposite
candidate. There is no local HALL shortfall caused ONLY by
opposite-target reuse in n=2; candidate eligibility is still open. -/
theorem actual_two_colour_earliest_loss_opposite_image_card_eq_debt
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (2 + 1))
    (exponent : V → ℕ) (choice : V → Fin 2) :
    ((actualEarliestLossCollisionRecords C exponent choice).image
      (fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)).card =
      translatedLossDuplicateDebt C exponent choice := by
  classical
  calc
    ((actualEarliestLossCollisionRecords C exponent choice).image
      (fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)).card =
      (actualEarliestLossCollisionRecords C exponent choice).card :=
        Finset.card_image_of_injOn
          (actual_two_colour_earliest_loss_opposite_injOn C exponent choice)
    _ = translatedLossDuplicateDebt C exponent choice :=
      actual_earliest_collision_records_card_eq_duplicate_debt
        C exponent choice

/-- In two colours, if EVERY original opposite candidate is indeed a
TRUE outside-translated hole, the complete ORIGINAL duplicate debt
is paid by distinct holes within its OWN collision squares. No
extra candidate-injectivity hypothesis is needed: it was proved
unconditionally above. Other seven debt classes can still compete
for the same holes, and the full planar payment remains OPEN. -/
theorem actual_two_colour_local_true_holes_pay_duplicate_of_all_candidates_real
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (2 + 1))
    (exponent : V → ℕ) (choice : V → Fin 2)
    (hreal :
      ∀ q ∈ ((actualEarliestLossCollisionRecords C exponent choice).image
        (fun a =>
          flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)),
        q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice) :
    translatedLossDuplicateDebt C exponent choice =
      ((actualEarliestLossCollisionRecords C exponent choice).biUnion
        (fun a =>
          lossCollisionSquareWords 2 a ∩
            lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  let Q := lossLedgerOutsideTranslatedTrueHoles C exponent choice
  let opp : Fin 2 × Fin 2 × (Fin 2 → Bool) → (Fin 2 → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  have hlocal := actual_earliest_loss_collision_local_holes_exact_image_inter
    C exponent choice
  have hinter : S.image opp ∩ Q = S.image opp := by
    ext q
    constructor
    · intro h
      exact (Finset.mem_inter.mp h).1
    · intro h
      exact Finset.mem_inter.mpr ⟨h, hreal q h⟩
  rw [hlocal, hinter]
  exact (actual_two_colour_earliest_loss_opposite_image_card_eq_debt
    C exponent choice).symm

#print axioms actual_two_colour_local_true_holes_pay_duplicate_of_all_candidates_real
#print axioms actual_loss_duplicate_debt_zero_of_one_colour
#print axioms actual_earliest_loss_two_colour_record_only_pair
#print axioms actual_two_colour_earliest_loss_opposite_injOn
#print axioms actual_two_colour_earliest_loss_opposite_image_card_eq_debt

end OrderedEdgeColoring
end JSP000404Research
