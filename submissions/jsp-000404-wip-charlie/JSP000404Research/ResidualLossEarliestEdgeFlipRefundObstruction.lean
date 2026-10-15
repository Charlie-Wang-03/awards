import JSP000404Research.ResidualLossEarliestEdgePaymentSeparation
import JSP000404Research.TranslatedCompletionCore
import Mathlib.Tactic

/-!
# Chosen-coordinate flip cannot refund a translated-loss debt into a true hole

Every Boolean word of a translated projected-loss slice is a
chosen-coordinate flip of a genuine retained completion word. Flipping
the chosen coordinate BACK necessarily lands in the already COVERED
completion union, never in a global true hole.

In particular a real first-occurrence source/blocker collision word
does not yield a true-hole refund by undoing the chosen flip. This rules
out a tempting but invalid local self-payment construction; it does
NOT rule out other mappings, nor prove the six-source payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Flipping back at the chosen coordinate of ANY translated-loss
word lands in the original covered completion union. -/
theorem lossSlice_chosenFlip_is_covered
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (c : Fin n) {word : Fin n → Bool}
    (hword : word ∈ translatedLossSliceWords C exponent choice c) :
    flipBoolWordAt word c ∈ coveredCompletionWords C := by
  classical
  obtain ⟨v, hv, hvword⟩ := Finset.mem_biUnion.mp hword
  have hcomp :=
    (mem_translatedCompletionWords C v c word).1 hvword
  apply (mem_coveredCompletionWords C _).2
  exact ⟨v, (mem_completionFibre C _ v).2 hcomp⟩

/-- The actual first-occurrence edge carrier has its chosen-coordinate
flip in the COVERED union. It is not an outside or inside true hole. -/
theorem lossEarliestActualEdgeCarrier_chosenFlip_is_covered
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (c d : Fin n) (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hword : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p) :
    flipBoolWordAt word c ∈ coveredCompletionWords C := by
  classical
  have hearly :=
    lossEarliestActualEdgeCarrier_subset_earliestPair
      C exponent choice c d p hp hword
  have hs :
      word ∈ lossSliceAtNat C exponent choice c.val :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hearly).1).1
  have hc :
      word ∈ translatedLossSliceWords C exponent choice c := by
    simpa [lossSliceAtNat, c.isLt] using hs
  exact lossSlice_chosenFlip_is_covered
    C exponent choice c hc

/-- The reverse chosen-coordinate flip of a genuine first-hit
collision word is NOT a true-hole refund. -/
theorem lossEarliestActualEdgeCarrier_chosenFlip_not_trueHole
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (c d : Fin n) (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hword : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p) :
    flipBoolWordAt word c ∉ lossLedgerGlobalTrueHoles C := by
  intro hh
  have hc :=
    lossEarliestActualEdgeCarrier_chosenFlip_is_covered
      C exponent choice c d p hp hword
  exact (Finset.mem_sdiff.mp hh).2 hc

#print axioms lossSlice_chosenFlip_is_covered
#print axioms lossEarliestActualEdgeCarrier_chosenFlip_is_covered
#print axioms lossEarliestActualEdgeCarrier_chosenFlip_not_trueHole

end OrderedEdgeColoring
end JSP000404Research
