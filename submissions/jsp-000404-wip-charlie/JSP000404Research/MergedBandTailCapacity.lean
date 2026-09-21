import JSP000404Research.TailMajorizationCapacity
import JSP000404Research.MergedBandMap
import Mathlib.Tactic

/-!
# Tail-majorization for binary edge partitions and the merged wrap partition

TailMajorizationCapacity was first stated for OrderedEdgeColoring, but the
layer-cake argument only needs weighted Hansel capacity.  BinaryEdgePartition
has the same weighted capacity and is the natural target of the merged-wrap
construction.

For the canonical lower-branch partition obtained by merging standard bands
0 and n, the full arbitrary-cardinality lower branch is therefore reduced to
one family of threshold inequalities:

  #{v | r < exponent(v)}
    <=
  #{v | r < n - active_merged(v)}

for every r<n.

This is strictly weaker than requiring active_merged(v) <= n-exponent(v) at
every vertex.  Losses at one centre may be paid by extra free coordinates at
other centres.
-/

namespace JSP000404Research

open scoped BigOperators

namespace BinaryEdgePartition

theorem exponent_capacity_of_tail_domination
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : BinaryEdgePartition V n)
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (htail :
      ∀ r < n,
        tailCount exponent r ≤
          tailCount
            (fun v => n - (active C v).card) r) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  have hfree :
      ∀ v, n - (active C v).card ≤ n := by
    intro v
    omega
  have hprofile :=
    dyadic_sum_le_of_tailCount_le
      exponent
      (fun v => n - (active C v).card)
      n hexp hfree htail
  exact hprofile.trans C.weighted_capacity

theorem exponent_capacity_of_threshold_counts
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : BinaryEdgePartition V n)
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hcount :
      ∀ r < n,
        ((Finset.univ : Finset V).filter
          (fun v => r < exponent v)).card
        ≤
        ((Finset.univ : Finset V).filter
          (fun v => r <
            n - (active C v).card)).card) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  apply exponent_capacity_of_tail_domination C exponent hexp
  intro r hr
  exact hcount r hr

#print axioms exponent_capacity_of_tail_domination
#print axioms exponent_capacity_of_threshold_counts

end BinaryEdgePartition

namespace DirectionData

/-- Final profile-level outlet for the deterministic merged-wrap partition. -/
theorem canonicalFixedPhase_capacity_of_tail_domination
    {V : Type*} [LinearOrder V] [Fintype V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (htail :
      ∀ r < n,
        tailCount exponent r ≤
          tailCount
            (fun v =>
              n -
                (BinaryEdgePartition.active
                  (canonicalFixedPhasePartition
                    D hwidth hdelta hn htri) v).card)
            r) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  exact BinaryEdgePartition.exponent_capacity_of_tail_domination
    (canonicalFixedPhasePartition D hwidth hdelta hn htri)
    exponent hexp htail

/-- Same outlet in filtered-cardinality form, designed for phase/hull counting
arguments. -/
theorem canonicalFixedPhase_capacity_of_threshold_counts
    {V : Type*} [LinearOrder V] [Fintype V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hcount :
      ∀ r < n,
        ((Finset.univ : Finset V).filter
          (fun v => r < exponent v)).card
        ≤
        ((Finset.univ : Finset V).filter
          (fun v => r <
            n -
              (BinaryEdgePartition.active
                (canonicalFixedPhasePartition
                  D hwidth hdelta hn htri) v).card)).card) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  exact BinaryEdgePartition.exponent_capacity_of_threshold_counts
    (canonicalFixedPhasePartition D hwidth hdelta hn htri)
    exponent hexp hcount

#print axioms canonicalFixedPhase_capacity_of_tail_domination
#print axioms canonicalFixedPhase_capacity_of_threshold_counts

end DirectionData

end JSP000404Research
