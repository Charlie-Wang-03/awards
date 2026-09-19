import JSP000404Research.WeightedDefect
import Mathlib.Tactic

/-!
# Binary edge-partition certificate with local colour incidence

A sharp weighted Kraft bound follows from a configuration-dependent partition
of the complete ordered graph into `k` binary-colourable parts.

For every increasing edge `v < w`, `edgeColor v w` chooses one coordinate
and `proper` says that the two endpoints receive opposite Boolean bits in
that coordinate.  A vertex only specifies coordinates of colours actually
incident to it.

The geometric JSP-000404 bridge can therefore be stated concretely as:
construct such an edge partition with at most `ell v` active colours at
centre `v`.  If `ell v = k - exponent v`, the weighted Hansel inequality
immediately gives `sum 2^(exponent v) <= 2^k`.
-/

namespace JSP000404Research

open scoped BigOperators

structure BinaryEdgePartition (V : Type*) [LinearOrder V] (k : ℕ) where
  edgeColor : V → V → Fin k
  bit : V → Fin k → Bool
  proper : ∀ {v w : V}, v < w →
    bit v (edgeColor v w) ≠ bit w (edgeColor v w)

namespace BinaryEdgePartition

/-- Colours of edges incident to a vertex. -/
noncomputable def active {V : Type*} [LinearOrder V] {k : ℕ}
    (C : BinaryEdgePartition V k) (v : V) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun c ↦
    (∃ a, a < v ∧ C.edgeColor a v = c) ∨
    (∃ w, v < w ∧ C.edgeColor v w = c)

/-- Every pair is separated on the colour assigned to its edge. -/
theorem separates
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : BinaryEdgePartition V k) :
    ∀ v w, v ≠ w → ∃ c,
      c ∈ active C v ∧ c ∈ active C w ∧ C.bit v c ≠ C.bit w c := by
  classical
  intro v w hvw
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · let c := C.edgeColor v w
    refine ⟨c, ?_, ?_, ?_⟩
    · simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨w, hvwlt, rfl⟩
    · simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨v, hvwlt, rfl⟩
    · exact C.proper hvwlt
  · let c := C.edgeColor w v
    refine ⟨c, ?_, ?_, ?_⟩
    · simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨w, hwvlt, rfl⟩
    · simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨v, hwvlt, rfl⟩
    · exact (C.proper hwvlt).symm

/-- Weighted capacity of a binary edge partition. -/
theorem weighted_capacity
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : BinaryEdgePartition V k) :
    ∑ v, 2 ^ (k - (active C v).card) ≤ 2 ^ k := by
  exact weighted_hansel C.bit (active C) (separates C)

/-- Exact defect form. -/
theorem defect
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : BinaryEdgePartition V k) :
    ∑ v, (2 ^ (k - (active C v).card) - 1) ≤
      2 ^ k - Fintype.card V := by
  exact weighted_hansel_defect C.bit (active C) (separates C)

/-- If the active-colour count at `v` is at most a prescribed deficit
`ell v`, then the represented subcube has at least the expected weight
`2^(k-ell v)`. -/
theorem expected_weight_le
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : BinaryEdgePartition V k) (ell : V → ℕ)
    (hactive : ∀ v, (active C v).card ≤ ell v) :
    ∑ v, 2 ^ (k - ell v) ≤ ∑ v, 2 ^ (k - (active C v).card) := by
  apply Finset.sum_le_sum
  intro v _
  apply Nat.pow_le_pow_right
  · norm_num
  · omega

/-- Local incidence bounds imply the Kraft inequality. -/
theorem capacity_of_active_le
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : BinaryEdgePartition V k) (ell : V → ℕ)
    (hactive : ∀ v, (active C v).card ≤ ell v) :
    ∑ v, 2 ^ (k - ell v) ≤ 2 ^ k :=
  (expected_weight_le C ell hactive).trans (weighted_capacity C)

/-- Cluster-exponent form used by the Sendov reduction. -/
theorem cluster_capacity_of_active_le
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : BinaryEdgePartition V k)
    (exponent ell : V → ℕ)
    (hexponent : ∀ v, exponent v ≤ k)
    (hell : ∀ v, ell v = k - exponent v)
    (hactive : ∀ v, (active C v).card ≤ ell v) :
    ∑ v, 2 ^ exponent v ≤ 2 ^ k := by
  calc
    ∑ v, 2 ^ exponent v =
        ∑ v, 2 ^ (k - ell v) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [hell v, Nat.sub_sub_cancel (hexponent v)]
    _ ≤ 2 ^ k := capacity_of_active_le C ell hactive

/-- Any proper partition of all complete-graph edges into `k` binary
colour classes gives the ordinary Hansel cardinality bound. -/
theorem card_le_two_pow
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : BinaryEdgePartition V k) :
    Fintype.card V ≤ 2 ^ k := by
  have hcap := weighted_capacity C
  have hone :
      Fintype.card V ≤ ∑ v, 2 ^ (k - (active C v).card) := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset V))
        (fun v _ => Nat.one_le_pow _ _))
  exact hone.trans hcap

#print axioms separates
#print axioms weighted_capacity
#print axioms card_le_two_pow
#print axioms defect
#print axioms expected_weight_le
#print axioms capacity_of_active_le
#print axioms cluster_capacity_of_active_le

end BinaryEdgePartition
end JSP000404Research
