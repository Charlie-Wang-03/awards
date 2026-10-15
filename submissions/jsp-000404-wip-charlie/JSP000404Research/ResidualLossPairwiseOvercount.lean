import JSP000404Research.ResidualLossCrossSliceCarrier
import JSP000404Research.ResidualLossDuplicateDebtLedger
import Mathlib.Tactic

/-!
# Pairwise upper bound for duplicate loss mass

The overcount caused by combining a finite sequence of Boolean-word
finsets never exceeds the sum of pairwise intersections.

This is a universal finite-set statement, independent of geometric
AngleCap, and cannot itself produce outside true holes or surplus.

First work with a natural prefix, to keep the exact telescoping argument
and each old/new intersection visible to Lean.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Union of the first k finite slices. -/
noncomputable def lossPrefixUnion
    {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (k : ℕ) : Finset α :=
  (Finset.range k).biUnion A

/-- The union's overlap with the new slice is paid by pairwise
intersections with the preceding slices. This is ONLY a bound on
double counting, not a globally non-reusing terminal payment. -/
theorem lossPrefixUnion_inter_card_le_pairwise
    {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (k : ℕ) :
    (lossPrefixUnion A k ∩ A k).card ≤
      ∑ j ∈ Finset.range k, (A k ∩ A j).card := by
  classical
  have heq :
      lossPrefixUnion A k ∩ A k =
        (Finset.range k).biUnion (fun j => A k ∩ A j) := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨hU, hk⟩ := Finset.mem_inter.mp hx
      obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hU
      exact Finset.mem_biUnion.mpr
        ⟨j, hj, Finset.mem_inter.mpr ⟨hk, hxj⟩⟩
    · intro x hx
      obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hk, hjx⟩ := Finset.mem_inter.mp hxj
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨j, hj, hjx⟩, hk⟩
  rw [heq]
  exact Finset.card_biUnion_le

/-- General finite-prefix Bonferroni-type bound:
sum of individual slice cardinalities is at most the union
cardinality plus all PREVIOUS-vs-NEW pair intersections. -/
theorem lossSumCard_le_prefixUnion_add_pairwise
    {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (k : ℕ) :
    (∑ i ∈ Finset.range k, (A i).card) ≤
      (lossPrefixUnion A k).card +
        ∑ i ∈ Finset.range k,
          ∑ j ∈ Finset.range i, (A i ∩ A j).card := by
  classical
  induction k with
  | zero =>
      simp [lossPrefixUnion]
  | succ k ih =>
      have hunion :
          lossPrefixUnion A (k + 1) =
            lossPrefixUnion A k ∪ A k := by
        simp [lossPrefixUnion, Finset.range_add_one, Finset.union_comm]
      have hcard :=
        Finset.card_union_add_card_inter (lossPrefixUnion A k) (A k)
      have hinter :=
        lossPrefixUnion_inter_card_le_pairwise A k
      simp only [Finset.sum_range_succ, hunion]
      omega

/-- Exact, rather than upper-bound, finite-union overcount:
each new slice contributes precisely its overlap with the union
of all earlier slices. There is no pairwise multiple counting in
this ledger identity. -/
theorem lossSumCard_eq_prefixUnion_add_priorOverlap
    {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (k : ℕ) :
    (∑ i ∈ Finset.range k, (A i).card) =
      (lossPrefixUnion A k).card +
        ∑ i ∈ Finset.range k,
          (A i ∩ lossPrefixUnion A i).card := by
  classical
  induction k with
  | zero =>
      simp [lossPrefixUnion]
  | succ k ih =>
      have hunion :
          lossPrefixUnion A (k + 1) =
            lossPrefixUnion A k ∪ A k := by
        simp [lossPrefixUnion, Finset.range_add_one, Finset.union_comm]
      have hcard :=
        Finset.card_union_add_card_inter (lossPrefixUnion A k) (A k)
      have hcomm :
          (A k ∩ lossPrefixUnion A k).card =
            (lossPrefixUnion A k ∩ A k).card := by
        rw [Finset.inter_comm]
      simp only [Finset.sum_range_succ, hunion]
      omega

#print axioms lossSumCard_eq_prefixUnion_add_priorOverlap

/-- Translate the actual chosen-coordinate loss slice to the natural
index `i`; outside Fin n it is explicitly empty. -/
noncomputable def lossSliceAtNat
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (i : ℕ) : Finset (Fin n → Bool) :=
  if hi : i < n then
    translatedLossSliceWords C exponent choice ⟨i, hi⟩
  else ∅

/-- Indexing all loss slices by the natural prefix counts every
original Fin n slice exactly once. -/
theorem lossSliceAtNat_sum_card_eq_fin_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    (∑ i ∈ Finset.range n,
      (lossSliceAtNat C exponent choice i).card) =
      ∑ c : Fin n,
        (translatedLossSliceWords C exponent choice c).card := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  simp [lossSliceAtNat, hin]

/-- The union of natural-index slices agrees exactly with the
already certified Boolean union in the projected-loss ledger. -/
theorem lossSliceAtNat_prefix_union_eq_loss_union
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    lossPrefixUnion (lossSliceAtNat C exponent choice) n =
      translatedLossAllCoordinateWords C exponent choice := by
  classical
  unfold lossPrefixUnion translatedLossAllCoordinateWords
  ext word
  constructor
  · intro h
    obtain ⟨i, hi, hword⟩ := Finset.mem_biUnion.mp h
    have hin : i < n := Finset.mem_range.mp hi
    apply Finset.mem_biUnion.mpr
    refine ⟨(⟨i, hin⟩ : Fin n), Finset.mem_univ _, ?_⟩
    simpa [lossSliceAtNat, hin] using hword
  · intro h
    obtain ⟨c, _hc, hword⟩ := Finset.mem_biUnion.mp h
    apply Finset.mem_biUnion.mpr
    refine ⟨c.val, Finset.mem_range.mpr c.isLt, ?_⟩
    simpa [lossSliceAtNat, c.isLt] using hword

/-- The real global duplicate debt is bounded by the sum of
two-coordinate Boolean-slice intersections, each unordered coordinate
pair counted exactly once. This is unconditional combinatorial
bookkeeping, NOT the terminal global true-hole payment. -/
theorem translatedLossDuplicateDebt_le_pairwise_slices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice ≤
      ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range i,
          (lossSliceAtNat C exponent choice i ∩
            lossSliceAtNat C exponent choice j).card := by
  classical
  have hbound :=
    lossSumCard_le_prefixUnion_add_pairwise
      (lossSliceAtNat C exponent choice) n
  rw [lossSliceAtNat_sum_card_eq_fin_sum,
    lossSliceAtNat_prefix_union_eq_loss_union] at hbound
  unfold translatedLossDuplicateDebt
  omega

/-- Exact first-occurrence decomposition of the ORIGINAL global
duplicate debt, using increasing natural coordinate indices.
Repeated words can contribute on successive later coordinate slices;
no claim about global outside holes or payment is needed. -/
theorem translatedLossDuplicateDebt_eq_sum_prior_coordinate_overlaps
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice =
      ∑ i ∈ Finset.range n,
        (lossSliceAtNat C exponent choice i ∩
          lossPrefixUnion (lossSliceAtNat C exponent choice) i).card := by
  classical
  have hexact :=
    lossSumCard_eq_prefixUnion_add_priorOverlap
      (lossSliceAtNat C exponent choice) n
  rw [lossSliceAtNat_sum_card_eq_fin_sum,
    lossSliceAtNat_prefix_union_eq_loss_union] at hexact
  unfold translatedLossDuplicateDebt
  omega

#print axioms translatedLossDuplicateDebt_eq_sum_prior_coordinate_overlaps

#print axioms lossSliceAtNat_sum_card_eq_fin_sum
#print axioms lossSliceAtNat_prefix_union_eq_loss_union
#print axioms translatedLossDuplicateDebt_le_pairwise_slices

#print axioms lossPrefixUnion_inter_card_le_pairwise
#print axioms lossSumCard_le_prefixUnion_add_pairwise

end OrderedEdgeColoring
end JSP000404Research
