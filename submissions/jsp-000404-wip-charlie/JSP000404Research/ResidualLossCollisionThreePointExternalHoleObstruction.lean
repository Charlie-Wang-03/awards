import JSP000404Research.ResidualLossCrossSliceTwoCoveredAncestors
import JSP000404Research.ResidualLossExternalHoleBudget
import Mathlib.Tactic

/-!
# Triple forbidden payment neighbourhood of a TRUE cross-slice loss collision

For every actual cross-coordinate translated-loss collision word `w`
with different chosen coordinates `c ≠ d`, neither `w` nor either
immediate chosen-coordinate Hamming neighbour `flip(w,c)`, `flip(w,d)`
may be a TRUE external hole-credit word:

* `w` is in the actual translated-loss union, so it is excluded from
  the OUTSIDE-TRANSLATED true-hole credit even if globally uncovered;
* both distinct immediate one-bit ancestors are ORIGINAL COVERED words;
* their covering status excludes both of them from true-hole credit.

Thus the three explicitly distinct local candidate words are disallowed
in the original global payment ledger. This is a genuine, unconditional
geometric/retained-coding exclusion for every such actual collision, not
an assumed candidate Hall relation or an invented source of holes.
It does not imply that a more remote true hole exists.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Changing any Boolean coordinate produces a different Boolean word. -/
theorem flipped_bool_word_ne_original
    {n : ℕ} (w : Fin n → Bool) (c : Fin n) :
    flipBoolWordAt w c ≠ w := by
  intro h
  have hc := congrArg (fun a : Fin n → Bool => a c) h
  rw [flipBoolWordAt_at] at hc
  cases hbit : w c <;> simp [hbit] at hc

/-- A REAL cross-slice collision forbids THREE distinct Boolean words as
outside-translated true-hole credits: the collision itself (because it lies
inside a translated-loss slice) and both covered one-bit ancestors. -/
theorem cross_loss_collision_three_distinct_non_external_holes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d)
    {word : Fin n → Bool}
    (hc : word ∈ translatedLossSliceWords C exponent choice c)
    (hd : word ∈ translatedLossSliceWords C exponent choice d) :
    word ∉ lossLedgerOutsideTranslatedTrueHoles C exponent choice ∧
    flipBoolWordAt word c ∉ lossLedgerOutsideTranslatedTrueHoles C exponent choice ∧
    flipBoolWordAt word d ∉ lossLedgerOutsideTranslatedTrueHoles C exponent choice ∧
    word ≠ flipBoolWordAt word c ∧
    word ≠ flipBoolWordAt word d ∧
    flipBoolWordAt word c ≠ flipBoolWordAt word d := by
  classical
  have htranslated : word ∈ translatedLossAllCoordinateWords
      C exponent choice := by
    unfold translatedLossAllCoordinateWords
    exact Finset.mem_biUnion.mpr
      ⟨c, Finset.mem_univ _, hc⟩
  have hwordOutside :
      word ∉ lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
    intro hw
    exact (Finset.mem_sdiff.mp hw).2 htranslated
  obtain ⟨hcCov,hdCov,hne⟩ :=
    crossLossCollision_two_distinct_covered_ancestors
      C exponent choice hcd hc hd
  have hleftOutside :
      flipBoolWordAt word c ∉
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
    intro h
    exact (Finset.mem_sdiff.mp
      (Finset.mem_sdiff.mp h).1).2 hcCov
  have hrightOutside :
      flipBoolWordAt word d ∉
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
    intro h
    exact (Finset.mem_sdiff.mp
      (Finset.mem_sdiff.mp h).1).2 hdCov
  exact ⟨hwordOutside,hleftOutside,hrightOutside,
    (flipped_bool_word_ne_original word c).symm,
    (flipped_bool_word_ne_original word d).symm,hne⟩

/-- The obstruction above applies to every genuine same-colour
source/blocker retained-edge carrier on two different chosen coordinates,
with no assumption that the collision belongs to the covered set. -/
theorem earliest_actual_edge_collision_three_external_hole_exclusions
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d)
    (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hword : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p) :
    word ∉ lossLedgerOutsideTranslatedTrueHoles C exponent choice ∧
    flipBoolWordAt word c ∉ lossLedgerOutsideTranslatedTrueHoles C exponent choice ∧
    flipBoolWordAt word d ∉ lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
  have hearly :=
    lossEarliestActualEdgeCarrier_subset_earliestPair
      C exponent choice c d p hp hword
  have hpair :=
    Finset.mem_inter.mp (Finset.mem_sdiff.mp hearly).1
  have hc : word ∈ translatedLossSliceWords C exponent choice c := by
    simpa [lossSliceAtNat, c.isLt] using hpair.1
  have hd : word ∈ translatedLossSliceWords C exponent choice d := by
    simpa [lossSliceAtNat, d.isLt] using hpair.2
  obtain ⟨hw, hcNoHole, hdNoHole, _, _, _⟩ :=
    cross_loss_collision_three_distinct_non_external_holes
      C exponent choice hcd hc hd
  exact ⟨hw, hcNoHole, hdNoHole⟩

#print axioms flipped_bool_word_ne_original
#print axioms cross_loss_collision_three_distinct_non_external_holes
#print axioms earliest_actual_edge_collision_three_external_hole_exclusions

end OrderedEdgeColoring
end JSP000404Research
