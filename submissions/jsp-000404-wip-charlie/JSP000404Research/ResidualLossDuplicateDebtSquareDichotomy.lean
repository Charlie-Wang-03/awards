import JSP000404Research.ResidualLossCollisionThreePointExternalHoleObstruction
import JSP000404Research.ResidualLossDuplicateDebtLedger
import Mathlib.Tactic

/-!
# Actual positive projected-loss duplicate debt forces a BAD four-corner square

This is the first bridge from the NUMERICAL duplicate-debt term that
appears literally in the sole remaining six-source global payment
inequality to concrete source-native forbidden true-hole credits.

Without ANY further combinatorial or planar assumptions:
 * either projected-loss translated-coordinate duplicate debt is zero,
 * or one can extract a REAL two-coordinate Boolean collision w,c,d
   such that the square consisting of w and its two one-bit ancestors
   plus its opposite two-bit corner has AT MOST ONE eligible exterior
   TRUE Boolean hole, namely the opposite corner.

The theorem is an obstruction/case split, NOT an injection or the
claim that the fourth corner is a true hole. Its unconditional
derivation means a proposed global refund argument must explicitly
handle this source-native deficient local candidate supply.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Every positive REAL projected-loss duplicate debt forces a genuine
coordinate-collision Hamming square with at most one TRUE exterior hole.
No additional hypothesis about retained edges is needed to extract
the collision: positive exact duplicate debt already guarantees it. -/
theorem positive_loss_duplicate_debt_forces_one_hole_square
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hpositive : 0 < translatedLossDuplicateDebt C exponent choice) :
    ∃ c d : Fin n, c ≠ d ∧
      ∃ word : Fin n → Bool,
        word ∈ translatedLossSliceWords C exponent choice c ∧
        word ∈ translatedLossSliceWords C exponent choice d ∧
        ((insert word
          (insert (flipBoolWordAt word c)
            (insert (flipBoolWordAt word d)
              ({flipBoolWordAt (flipBoolWordAt word c) d} :
                Finset (Fin n → Bool))))) ∩
            lossLedgerOutsideTranslatedTrueHoles C exponent choice).card
              ≤ 1 := by
  obtain ⟨c,d,hcd,word,hc,hd⟩ :=
    positive_loss_duplicateDebt_has_slice_collision
      C exponent choice hpositive
  refine ⟨c,d,hcd,word,hc,hd,?_⟩
  exact cross_loss_collision_square_external_holes_card_le_one
    C exponent choice hcd hc hd

/-- No positive source duplicate debt escapes the certified local
four-corner exclusion: this is an unconditional global branch
partition of the ORIGINAL exact duplicate-debt term. -/
theorem loss_duplicate_debt_zero_or_one_hole_collision_square
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice = 0 ∨
    ∃ c d : Fin n, c ≠ d ∧
      ∃ word : Fin n → Bool,
        word ∈ translatedLossSliceWords C exponent choice c ∧
        word ∈ translatedLossSliceWords C exponent choice d ∧
        ((insert word
          (insert (flipBoolWordAt word c)
            (insert (flipBoolWordAt word d)
              ({flipBoolWordAt (flipBoolWordAt word c) d} :
                Finset (Fin n → Bool))))) ∩
            lossLedgerOutsideTranslatedTrueHoles C exponent choice).card
              ≤ 1 := by
  by_cases hzero : translatedLossDuplicateDebt C exponent choice = 0
  · exact Or.inl hzero
  · exact Or.inr (positive_loss_duplicate_debt_forces_one_hole_square
      C exponent choice (Nat.pos_of_ne_zero hzero))

#print axioms positive_loss_duplicate_debt_forces_one_hole_square
#print axioms loss_duplicate_debt_zero_or_one_hole_collision_square

end OrderedEdgeColoring
end JSP000404Research
