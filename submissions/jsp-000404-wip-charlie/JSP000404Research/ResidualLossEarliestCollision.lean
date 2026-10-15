import JSP000404Research.ResidualLossPairwiseOvercount
import Mathlib.Tactic

/-!
# Exact earliest-prior-coordinate partition for loss duplicate events

For each later coordinate i, every word previously seen in a slice
has a unique earliest prior coordinate j < i. The new earliest-carrier
pieces subtract the union strictly before j.

This gives a double sum which is EXACTLY the original global
`translatedLossDuplicateDebt` rather than the potentially looser
sum of all pair intersections.

This proves no new true holes or unreserved surplus and does not
discharge the six-source terminal payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- An intersection word carried by coordinate j but unseen on
any *strictly* earlier coordinate than j. -/
noncomputable def lossEarliestPairWords
    {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (i j : ℕ) : Finset α :=
  (A i ∩ A j) \ lossPrefixUnion A j

/-- For a fixed later coordinate i, the earliest-prior-coordinate
pieces add up EXACTLY to its overlap with the earlier union.
The identity excludes any reuse within this i-slice. -/
theorem lossPrefixOverlap_card_eq_sum_earliestPairs
    {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (i k : ℕ) :
    (A i ∩ lossPrefixUnion A k).card =
      ∑ j ∈ Finset.range k, (lossEarliestPairWords A i j).card := by
  classical
  induction k with
  | zero =>
      simp [lossPrefixUnion]
  | succ k ih =>
      have hunion :
          lossPrefixUnion A (k + 1) =
            lossPrefixUnion A k ∪ A k := by
        simp [lossPrefixUnion, Finset.range_add_one, Finset.union_comm]
      have hdistrib :
          A i ∩ lossPrefixUnion A (k + 1) =
            (A i ∩ lossPrefixUnion A k) ∪ (A i ∩ A k) := by
        rw [hunion]
        ext word
        simp only [Finset.mem_inter, Finset.mem_union]
        tauto
      have hinter :
          ((A i ∩ lossPrefixUnion A k) ∩ (A i ∩ A k)) =
            ((A i ∩ A k) ∩ lossPrefixUnion A k) := by
        ext word
        simp only [Finset.mem_inter]
        tauto
      have hcard :=
        Finset.card_union_add_card_inter
          (A i ∩ lossPrefixUnion A k) (A i ∩ A k)
      rw [hinter] at hcard
      have hnew :=
        Finset.card_sdiff_add_card_inter
          (A i ∩ A k) (lossPrefixUnion A k)
      change
        ((A i ∩ A k) \ lossPrefixUnion A k).card +
          ((A i ∩ A k) ∩ lossPrefixUnion A k).card =
        (A i ∩ A k).card at hnew
      rw [hdistrib, Finset.sum_range_succ]
      change
        ((A i ∩ lossPrefixUnion A k) ∪ (A i ∩ A k)).card =
          (∑ j ∈ Finset.range k, (lossEarliestPairWords A i j).card) +
            ((A i ∩ A k) \ lossPrefixUnion A k).card
      omega

/-- Unconditional exact 2-index identity for the ORIGINAL
projected-loss duplicate-debt quantity, using first appearances rather
than charging a word to every earlier coordinate where it appeared. -/
theorem translatedLossDuplicateDebt_eq_sum_earliestPairWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice =
      ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range i,
          (lossEarliestPairWords
            (lossSliceAtNat C exponent choice) i j).card := by
  classical
  rw [translatedLossDuplicateDebt_eq_sum_prior_coordinate_overlaps]
  apply Finset.sum_congr rfl
  intro i hi
  exact lossPrefixOverlap_card_eq_sum_earliestPairs
    (lossSliceAtNat C exponent choice) i i

#print axioms lossPrefixOverlap_card_eq_sum_earliestPairs
#print axioms translatedLossDuplicateDebt_eq_sum_earliestPairWords

end OrderedEdgeColoring
end JSP000404Research
