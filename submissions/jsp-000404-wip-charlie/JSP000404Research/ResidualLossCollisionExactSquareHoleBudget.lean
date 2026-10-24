import JSP000404Research.ResidualLossCollisionThreePointExternalHoleObstruction
import Mathlib.Tactic

/-!
# Exact local external true-hole budget for a genuine loss-collision square

A translated-loss coordinate collision is not a source of three or four
new Boolean holes. Of the original four two-coordinate cube-square
corners, three are CERTIFIED ineligible for true exterior-hole credit.

The remaining (double-flip) corner contributes EXACTLY one external
true hole if it actually belongs to the ORIGINAL exterior true-hole
ledger and otherwise contributes ZERO. This is not a new counting
assumption: the finite set of locally eligible words is literally
the singleton intersection with the original hole set.

This upgrades a conditional upper bound into a precise 0/1 identity,
without pretending the opposite corner is uncovered, without
allowing shared hole targets to be paid more than once, and without
proving the outstanding all-centre six-source global payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The only possibly externally payable word in an ACTUAL
two-coordinate translated-loss collision square is its double-flip
corner. The set equality preserves the true original Boolean-hole
predicate rather than creating any artificial local hole credits. -/
theorem cross_loss_collision_square_exterior_holes_exact_singleton
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d)
    {word : Fin n → Bool}
    (hc : word ∈ translatedLossSliceWords C exponent choice c)
    (hd : word ∈ translatedLossSliceWords C exponent choice d) :
    (insert word
      (insert (flipBoolWordAt word c)
        (insert (flipBoolWordAt word d)
          ({flipBoolWordAt (flipBoolWordAt word c) d} :
            Finset (Fin n → Bool))))) ∩
      lossLedgerOutsideTranslatedTrueHoles C exponent choice =
    ({flipBoolWordAt (flipBoolWordAt word c) d} :
      Finset (Fin n → Bool)) ∩
      lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
  classical
  ext target
  constructor
  · intro htarget
    obtain ⟨hsquare,hhole⟩ := Finset.mem_inter.mp htarget
    have heq :=
      cross_loss_collision_square_external_hole_only_double_flip
        C exponent choice hcd hc hd hsquare hhole
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_singleton.mpr heq, hhole⟩
  · intro htarget
    obtain ⟨hsingle,hhole⟩ := Finset.mem_inter.mp htarget
    have heq := Finset.mem_singleton.mp hsingle
    subst target
    refine Finset.mem_inter.mpr ⟨?_,hhole⟩
    simp

/-- EXACT local collision-square count: one if the remaining opposite
word is a verified original exterior true hole, otherwise zero. -/
theorem cross_loss_collision_square_exterior_holes_exact_count
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d)
    {word : Fin n → Bool}
    (hc : word ∈ translatedLossSliceWords C exponent choice c)
    (hd : word ∈ translatedLossSliceWords C exponent choice d) :
    ((insert word
      (insert (flipBoolWordAt word c)
        (insert (flipBoolWordAt word d)
          ({flipBoolWordAt (flipBoolWordAt word c) d} :
            Finset (Fin n → Bool))))) ∩
      lossLedgerOutsideTranslatedTrueHoles C exponent choice).card =
        if flipBoolWordAt (flipBoolWordAt word c) d ∈
          lossLedgerOutsideTranslatedTrueHoles C exponent choice
        then 1 else 0 := by
  classical
  rw [cross_loss_collision_square_exterior_holes_exact_singleton
    C exponent choice hcd hc hd]
  by_cases hq :
      flipBoolWordAt (flipBoolWordAt word c) d ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice
  · simp [hq]
  · simp [hq]

#print axioms cross_loss_collision_square_exterior_holes_exact_singleton
#print axioms cross_loss_collision_square_exterior_holes_exact_count

end OrderedEdgeColoring
end JSP000404Research
