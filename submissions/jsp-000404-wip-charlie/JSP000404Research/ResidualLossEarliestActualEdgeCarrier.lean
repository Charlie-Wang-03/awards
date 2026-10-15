import JSP000404Research.ResidualLossEarliestCollision
import JSP000404Research.ResidualLossCrossSliceCarrier
import Mathlib.Tactic

/-!
# Earliest-prior cross-coordinate collision mass carried by actual edges

For a fixed later coordinate i, the earliest prior coordinate j
partitions repeated words into disjoint finite cells.
Within every fixed coordinate pair (i,j), the exact collision pair
carriers have uniquely determined source and blocker owners, and are
pairwise disjoint. Restricting them to words not previously seen
before j preserves disjointness.

Consequently the full GLOBAL duplicate debt has an EXACT, finite
edge-local representation, not just a conservative dyadic upper bound.
The SAME Boolean word can contribute to multiple later i coordinates;
this proof does not create unreserved surplus or disjoint global
hole payments.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Earliest previous coordinate cannot be both j and k. -/
theorem lossEarliestPairWords_disjoint_of_lt
    {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (i : ℕ) {j k : ℕ}
    (hjk : j < k) :
    Disjoint (lossEarliestPairWords A i j)
      (lossEarliestPairWords A i k) := by
  classical
  rw [Finset.disjoint_left]
  intro word hwj hwk
  have hj := Finset.mem_sdiff.mp hwj
  have hk := Finset.mem_sdiff.mp hwk
  have hprefix : word ∈ lossPrefixUnion A k := by
    unfold lossPrefixUnion
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_range.mpr hjk,
        (Finset.mem_inter.mp hj.1).2⟩
  exact hk.2 hprefix

/-- For each later coordinate i, first-hit prior coordinates
give a genuinely pairwise disjoint partition of the repeated
words. A word may nevertheless recur for a different later i. -/
theorem lossEarliestPairWords_pairwiseDisjoint
    {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (i : ℕ) :
    (((Finset.range i : Finset ℕ) : Set ℕ)).PairwiseDisjoint
      (lossEarliestPairWords A i) := by
  classical
  intro j hj k hk hjk
  change Disjoint (lossEarliestPairWords A i j)
    (lossEarliestPairWords A i k)
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · exact lossEarliestPairWords_disjoint_of_lt A i hlt
  · exact (lossEarliestPairWords_disjoint_of_lt A i hgt).symm

/-- The TRUE two-coordinate collision words of an actual pair,
with every word previously appearing at a coordinate < d excluded.
The filtered intersection is a real source--blocker edge carrier,
not a Boolean hole. -/
noncomputable def lossEarliestActualEdgeCarrier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (c d : Fin n) (p : V × V) : Finset (Fin n → Bool) :=
  crossLossPairWords C c d p \
    lossPrefixUnion (lossSliceAtNat C exponent choice) d.val

/-- Earliest-prior collision words equal a union indexed by the
actual source--blocker pairs, with NO invented conflict pairs. -/
theorem lossEarliestPairWords_eq_biUnion_actualEdge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (c d : Fin n) :
    lossEarliestPairWords (lossSliceAtNat C exponent choice)
      c.val d.val =
    (crossLossConflictPairs C exponent choice c d).biUnion
      (lossEarliestActualEdgeCarrier C exponent choice c d) := by
  classical
  have hcslice :
      lossSliceAtNat C exponent choice c.val =
        translatedLossSliceWords C exponent choice c := by
    simp [lossSliceAtNat, c.isLt]
  have hdslice :
      lossSliceAtNat C exponent choice d.val =
        translatedLossSliceWords C exponent choice d := by
    simp [lossSliceAtNat, d.isLt]
  ext word
  constructor
  · intro hw
    have hparts := Finset.mem_sdiff.mp hw
    have hword :
        word ∈ translatedLossSliceWords C exponent choice c ∩
          translatedLossSliceWords C exponent choice d := by
      simpa only [lossEarliestPairWords, hcslice, hdslice] using hparts.1
    rw [crossTranslatedLossSlice_inter_eq_biUnion_pairs
      C exponent choice c d] at hword
    obtain ⟨p, hp, hpword⟩ := Finset.mem_biUnion.mp hword
    exact Finset.mem_biUnion.mpr
      ⟨p, hp, Finset.mem_sdiff.mpr ⟨hpword, hparts.2⟩⟩
  · intro hw
    obtain ⟨p, hp, hpword⟩ := Finset.mem_biUnion.mp hw
    have hboth := Finset.mem_sdiff.mp hpword
    have hword :
        word ∈ translatedLossSliceWords C exponent choice c ∩
          translatedLossSliceWords C exponent choice d := by
      rw [crossTranslatedLossSlice_inter_eq_biUnion_pairs
        C exponent choice c d]
      exact Finset.mem_biUnion.mpr ⟨p, hp, hboth.1⟩
    apply Finset.mem_sdiff.mpr
    exact ⟨by simpa [lossEarliestPairWords, hcslice, hdslice] using hword,
      hboth.2⟩

/-- Distinct effective source--blocker pairs have disjoint earliest
collision word sets within one fixed ordered pair (c,d). -/
theorem lossEarliestActualEdgeCarrier_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d) :
    (((crossLossConflictPairs C exponent choice c d : Finset (V × V)) :
      Set (V × V))).PairwiseDisjoint
      (lossEarliestActualEdgeCarrier C exponent choice c d) := by
  classical
  have hparent :=
    crossLossPairWords_pairwiseDisjoint
      C exponent hexp honeLoss choice hcd
  intro p hp q hq hpq
  change Disjoint (lossEarliestActualEdgeCarrier C exponent choice c d p)
    (lossEarliestActualEdgeCarrier C exponent choice c d q)
  have hdisj : Disjoint (crossLossPairWords C c d p)
      (crossLossPairWords C c d q) :=
    hparent hp hq hpq
  rw [Finset.disjoint_left]
  intro word hwp hwq
  exact Finset.disjoint_left.mp hdisj
    (Finset.mem_sdiff.mp hwp).1
    (Finset.mem_sdiff.mp hwq).1

/-- Exact actual-edge sum for each earliest coordinate pair.
The outer coordinate j is strictly the first previous occurrence,
while each effective source--blocker carrier has a unique word owner
within that pair. -/
theorem lossEarliestPairWords_card_eq_actualEdge_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d) :
    (lossEarliestPairWords
      (lossSliceAtNat C exponent choice) c.val d.val).card =
      ∑ p ∈ crossLossConflictPairs C exponent choice c d,
        (lossEarliestActualEdgeCarrier C exponent choice c d p).card := by
  classical
  rw [lossEarliestPairWords_eq_biUnion_actualEdge
    C exponent choice c d]
  rw [Finset.card_biUnion
    (lossEarliestActualEdgeCarrier_pairwiseDisjoint
      C exponent hexp honeLoss choice hcd)]

#print axioms lossEarliestPairWords_disjoint_of_lt
#print axioms lossEarliestPairWords_pairwiseDisjoint
#print axioms lossEarliestPairWords_eq_biUnion_actualEdge
#print axioms lossEarliestActualEdgeCarrier_pairwiseDisjoint
#print axioms lossEarliestPairWords_card_eq_actualEdge_sum

end OrderedEdgeColoring
end JSP000404Research
