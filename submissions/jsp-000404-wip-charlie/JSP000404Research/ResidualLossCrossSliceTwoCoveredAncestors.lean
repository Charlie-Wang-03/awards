import JSP000404Research.ResidualLossEarliestEdgeFlipRefundObstruction
import Mathlib.Tactic

/-!
# Two distinct COVERED ancestors of every true cross-coordinate collision

If a Boolean word occurs in loss slices of distinct chosen coordinates
c and d, undoing the c-flip and undoing the d-flip both land in the
ORIGINAL covered completion region, and yield distinct words.

This is a constraint on any proposed hole-refund involution:
neither of the two immediate chosen-coordinate neighbours is an
uncovered hole. The theorem is NOT a supply of new true holes,
nor a complete six-source payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Flipping a fixed Boolean word at two DISTINCT coordinates yields
two distinct Boolean words. -/
theorem flipBoolWordAt_ne_flipBoolWordAt_of_distinct
    {n : ℕ} (word : Fin n → Bool)
    {c d : Fin n} (hcd : c ≠ d) :
    flipBoolWordAt word c ≠ flipBoolWordAt word d := by
  intro h
  have hc := congrArg (fun w : Fin n → Bool => w c) h
  rw [flipBoolWordAt_at,
    flipBoolWordAt_off word hcd] at hc
  cases hb : word c <;> simp [hb] at hc

/-- Every genuine cross-coordinate translated-loss collision word
has TWO distinct neighbouring Boolean words already in the
covered original completion union. -/
theorem crossLossCollision_two_distinct_covered_ancestors
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d)
    {word : Fin n → Bool}
    (hc : word ∈ translatedLossSliceWords C exponent choice c)
    (hd : word ∈ translatedLossSliceWords C exponent choice d) :
    flipBoolWordAt word c ∈ coveredCompletionWords C ∧
      flipBoolWordAt word d ∈ coveredCompletionWords C ∧
      flipBoolWordAt word c ≠ flipBoolWordAt word d := by
  exact ⟨
    lossSlice_chosenFlip_is_covered C exponent choice c hc,
    lossSlice_chosenFlip_is_covered C exponent choice d hd,
    flipBoolWordAt_ne_flipBoolWordAt_of_distinct word hcd⟩

/-- The actual source/blocker earliest-carrier form of the same
two-distinct-covered-ancestor obstruction. -/
theorem lossEarliestActualEdgeCarrier_two_covered_ancestors
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d)
    (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hword : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p) :
    flipBoolWordAt word c ∈ coveredCompletionWords C ∧
      flipBoolWordAt word d ∈ coveredCompletionWords C ∧
      flipBoolWordAt word c ≠ flipBoolWordAt word d := by
  have hearly :=
    lossEarliestActualEdgeCarrier_subset_earliestPair
      C exponent choice c d p hp hword
  have hpair :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hearly).1)
  have hc :
      word ∈ translatedLossSliceWords C exponent choice c := by
    simpa [lossSliceAtNat, c.isLt] using hpair.1
  have hd :
      word ∈ translatedLossSliceWords C exponent choice d := by
    simpa [lossSliceAtNat, d.isLt] using hpair.2
  exact crossLossCollision_two_distinct_covered_ancestors
    C exponent choice hcd hc hd

#print axioms flipBoolWordAt_ne_flipBoolWordAt_of_distinct
#print axioms crossLossCollision_two_distinct_covered_ancestors
#print axioms lossEarliestActualEdgeCarrier_two_covered_ancestors

end OrderedEdgeColoring
end JSP000404Research
