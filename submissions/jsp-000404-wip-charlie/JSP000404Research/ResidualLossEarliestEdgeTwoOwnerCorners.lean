import JSP000404Research.ResidualLossCrossSliceTwoCoveredAncestors
import JSP000404Research.ResidualLossCrossSliceCoordinateRigidity
import Mathlib.Tactic

/-!
# Genuine collision words and their two different original-cube owners

For a true cross-coordinate loss collision word x carried by
a genuine ordered source/blocker pair p=(v,w), flipping the FIRST
coordinate maps x into the original retained cube of v; flipping
the SECOND maps x into the original retained cube of w.

If the chosen coordinates of both loss vertices are really retained
and ACTIVE, x is outside both of THOSE ORIGINAL cubes. The two
one-flip ancestors are different covered words owned by different
vertices.

This gives a source-native two-owner Hamming-corner obstruction
to naive local hole refunds. It does NOT prove that x itself is
globally uncovered, nor give a global matching to other holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A real cross-loss edge carrier supplies two distinct ORIGINAL
completion cubes at its two genuinely different endpoints, and
two different original covered words. -/
theorem lossEarliestActualEdgeCarrier_two_distinct_owner_ancestors
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d) (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hw : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p) :
    p.1 ≠ p.2 ∧
      flipBoolWordAt word c ∈ retainedCompletionWords C p.1 ∧
      flipBoolWordAt word d ∈ retainedCompletionWords C p.2 ∧
      flipBoolWordAt word c ≠ flipBoolWordAt word d := by
  classical
  have hlabels :=
    crossLossConflictPair_chosen_labels C exponent choice hp
  have hvw : p.1 ≠ p.2 := by
    intro h
    apply hcd
    calc
      c = choice p.1 := hlabels.1.symm
      _ = choice p.2 := congrArg choice h
      _ = d := hlabels.2
  have hparts :
      word ∈ translatedCompletionWords C p.1 c ∩
        translatedCompletionWords C p.2 d :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw).1) |>.elim
      (fun ha hb => Finset.mem_inter.mpr ⟨ha, hb⟩)
  exact ⟨hvw,
    (mem_translatedCompletionWords C p.1 c word).1
      (Finset.mem_inter.mp hparts).1,
    (mem_translatedCompletionWords C p.2 d word).1
      (Finset.mem_inter.mp hparts).2,
    flipBoolWordAt_ne_flipBoolWordAt_of_distinct word hcd⟩

/-- If all chosen loss coordinates are active, an actual collision
word lies in neither of the two original retained cubes of its
own source and blocker, even though both one-flip ancestors do. -/
theorem lossEarliestActualEdgeCarrier_outside_both_owner_cubes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    {c d : Fin n} (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hw : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p) :
    word ∉ retainedCompletionWords C p.1 ∧
      word ∉ retainedCompletionWords C p.2 := by
  classical
  have hdata :=
    (mem_crossLossConflictPairs
      C exponent choice c d p.1 p.2).1 hp
  have hlabels :=
    crossLossConflictPair_chosen_labels C exponent choice hp
  have hcactive : c ∈ retainedActive C p.1 := by
    rw [← hlabels.1]
    exact hchoice p.1
      ((mem_lossCoordinateSlice C exponent choice c p.1).1
        hdata.1).1
  have hdactive : d ∈ retainedActive C p.2 := by
    rw [← hlabels.2]
    exact hchoice p.2
      ((mem_lossCoordinateSlice C exponent choice d p.2).1
        hdata.2.1).1
  have hpair :=
    Finset.mem_inter.mp (Finset.mem_sdiff.mp hw).1
  constructor
  · intro horig
    exact Finset.disjoint_left.mp
      (translatedCompletionWords_disjoint_original_of_active
        C hcactive) hpair.1 horig
  · intro horig
    exact Finset.disjoint_left.mp
      (translatedCompletionWords_disjoint_original_of_active
        C hdactive) hpair.2 horig

#print axioms lossEarliestActualEdgeCarrier_two_distinct_owner_ancestors
#print axioms lossEarliestActualEdgeCarrier_outside_both_owner_cubes

end OrderedEdgeColoring
end JSP000404Research
