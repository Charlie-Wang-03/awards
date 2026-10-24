import JSP000404Research.ResidualLossCollisionExactSquareHoleBudget
import JSP000404Research.ResidualLossCollisionDoubleFlipExactTrueHole
import Mathlib.Tactic

/-!
# Exact actual-source test for a collision square to provide ONE genuine hole

This composes TWO independently sourced proofs:
(1) in an actual two-coordinate translated-loss collision square, the
exterior true-hole count is EXACTLY 0 or 1, solely decided by the
opposite double-flip Boolean word;
(2) for an actual earliest source/blocker retained edge, that opposite
word is a genuine exterior hole IFF both cross-activity conditions,
all third-party original-cube exclusions, and all translated-loss
reuse exclusions hold.

It gives a precise Boolean/geometry interface for one real collision
square. It is not an injection of DIFFERENT collision events into
distinct holes and cannot by itself discharge the global six-source
payment. No invented external hole credits or new axioms.
-/
namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A real earliest cross-coordinate collision square supplies EXACTLY
one true exterior Boolean hole if and only if the original two sources
are cross-active, every other retained cube misses the candidate, and
all translated-loss slices miss it. Otherwise it supplies zero holes. -/
theorem actual_loss_collision_square_one_hole_iff_eligible
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d)
    (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hw : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p) :
    Finset.card
      ((insert word
        (insert (flipBoolWordAt word c)
          (insert (flipBoolWordAt word d)
            ({flipBoolWordAt (flipBoolWordAt word c) d} :
              Finset (Fin n → Bool))))) ∩
        lossLedgerOutsideTranslatedTrueHoles C exponent choice) = 1 ↔
      d ∈ retainedActive C p.1 ∧
      c ∈ retainedActive C p.2 ∧
      (∀ z : V, z ≠ p.1 → z ≠ p.2 →
        flipBoolWordAt (flipBoolWordAt word c) d ∉
          retainedCompletionWords C z) ∧
      flipBoolWordAt (flipBoolWordAt word c) d ∉
        translatedLossAllCoordinateWords C exponent choice := by
  classical
  have hearly :=
    lossEarliestActualEdgeCarrier_subset_earliestPair
      C exponent choice c d p hp hw
  have hpair :=
    Finset.mem_inter.mp (Finset.mem_sdiff.mp hearly).1
  have hc : word ∈ translatedLossSliceWords C exponent choice c := by
    simpa [lossSliceAtNat, c.isLt] using hpair.1
  have hd : word ∈ translatedLossSliceWords C exponent choice d := by
    simpa [lossSliceAtNat, d.isLt] using hpair.2
  have hcount :=
    cross_loss_collision_square_exterior_holes_exact_count
      C exponent choice hcd hc hd
  have hiff :=
    actual_loss_collision_double_flip_external_hole_iff
      C exponent choice hcd p hp hw
  dsimp only at hiff
  rw [hcount]
  constructor
  · intro hOne
    have htrue :
        flipBoolWordAt (flipBoolWordAt word c) d ∈
          lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
      by_contra hnot
      simp [hnot] at hOne
    exact hiff.mp htrue
  · intro hreal
    have htrue := hiff.mpr hreal
    simp [htrue]

#print axioms actual_loss_collision_square_one_hole_iff_eligible

end OrderedEdgeColoring
end JSP000404Research
