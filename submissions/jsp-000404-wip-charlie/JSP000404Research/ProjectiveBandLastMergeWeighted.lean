
import JSP000404Research.ProjectiveBandLastMergeCapacity
import JSP000404Research.BinaryWeightedProfileRepair
import Mathlib.Tactic

/-!
# Weighted n+1 -> n projective-band compression

ProjectiveBandLastMergeCapacity gives a pointwise sufficient condition:
every centre saturating the old n+1-band budget must occupy both merged
boundary bands 0 and n.

That condition is stronger than necessary.  After the 0/n merge, let

  nu(v) = n - card(active_merged(v)).

The old one-layer bound

  card(active_old(v)) <= (n+1)-k(v)

and monotonicity of active palette under merging imply automatically

  k(v) <= nu(v)+1.

Thus the merged profile can lose at most one free coordinate at any centre.

WeightedProfileRepair then gives the strictly weaker global outlet:

  total one-layer loss weight <= total surplus credit

is already enough for the sharp n-bit capacity.

This permits some saturated centres to miss one of the two boundary bands,
provided their one-bit losses are paid elsewhere.  It is the direct
projective-band counterpart of BoundaryWeightedRepair.
-/

namespace JSP000404Research

open scoped BigOperators

namespace BinaryEdgePartition

/-- The active palette after the 0/n merge is exactly the image of the old
active palette under the merge map. -/
theorem mergeLastPartition_active_eq_image
    {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (v : V) :
    active (mergeLastPartition hn P wrapBit hwrap) v =
      (active P v).image (mergeLastColor hn) := by
  classical
  apply Finset.Subset.antisymm
  · exact mergeLastPartition_active_subset_image
      hn P wrapBit hwrap v
  · intro c hc
    obtain ⟨old, hold, rfl⟩ :=
      Finset.mem_image.mp hc
    simp only [active, Finset.mem_filter,
      Finset.mem_univ, true_and] at hold ⊢
    rcases hold with
      ⟨a, hav, hcol⟩ | ⟨w, hvw, hcol⟩
    · left
      refine ⟨a, hav, ?_⟩
      change
        mergeLastColor hn (P.edgeColor a v) =
          mergeLastColor hn old
      rw [hcol]
    · right
      refine ⟨w, hvw, ?_⟩
      change
        mergeLastColor hn (P.edgeColor v w) =
          mergeLastColor hn old
      rw [hcol]

/-- Exact cardinality form of the active-image identity. -/
theorem mergeLastPartition_active_card_eq_image
    {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (v : V) :
    (active (mergeLastPartition hn P wrapBit hwrap) v).card =
      ((active P v).image (mergeLastColor hn)).card := by
  rw [mergeLastPartition_active_eq_image
    hn P wrapBit hwrap v]

/-- The merged free profile is automatically within one layer of the target
exponent profile. -/
theorem exponent_le_mergedFree_add_one
    {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (exponent : V → ℕ)
    (hold :
      ∀ v, (active P v).card ≤
        (n + 1) - exponent v)
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v) :
    ∀ v,
      exponent v ≤
        (n -
          (active
            (mergeLastPartition hn P wrapBit hwrap)
            v).card) + 1 := by
  intro v
  have hmono :=
    mergeLastPartition_active_card_le
      hn P wrapBit hwrap v
  have holdv := hold v
  omega

/-- Main weighted compression theorem.  Pointwise saturation payment is
replaced by one aggregate dyadic repair inequality. -/
theorem cluster_capacity_of_last_merge_weighted_repair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (exponent : V → ℕ)
    (hold :
      ∀ v, (active P v).card ≤
        (n + 1) - exponent v)
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (hrepair :
      let M := mergeLastPartition hn P wrapBit hwrap
      oneLayerLossWeight exponent
          (fun v => n - (active M v).card)
        ≤
      oneLayerSurplusCredit exponent
          (fun v => n - (active M v).card)) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  let M := mergeLastPartition hn P wrapBit hwrap
  have hone :
      ∀ v,
        exponent v ≤
          (n - (active M v).card) + 1 := by
    simpa [M] using
      exponent_le_mergedFree_add_one
        hn P exponent hold wrapBit hwrap
  exact M.exponent_capacity_of_oneLayer_weighted_repair
    exponent hone (by simpa [M] using hrepair)

#print axioms mergeLastPartition_active_eq_image
#print axioms exponent_le_mergedFree_add_one
#print axioms cluster_capacity_of_last_merge_weighted_repair

end BinaryEdgePartition

/-- Concrete direct-projective specialization of the weighted final outlet. -/
theorem projectiveBand_capacity_of_last_merge_weighted_repair
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t delta lam : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (wrapBit : V → Bool)
    (hwrap :
      let P :=
        projectiveBandPartition hp hcap htpos hlam n
          (by
            rw [ht]
            push_cast
            linarith)
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (hrepair :
      let htop : t < (n + 1 : ℕ) := by
        rw [ht]
        push_cast
        linarith
      let P :=
        projectiveBandPartition hp hcap htpos hlam n htop
      let M :=
        BinaryEdgePartition.mergeLastPartition
          hn P wrapBit (by simpa [P, htop] using hwrap)
      oneLayerLossWeight
          (fun i => centreExponent (C i) t)
          (fun i => n - (BinaryEdgePartition.active M i).card)
        ≤
      oneLayerSurplusCredit
          (fun i => centreExponent (C i) t)
          (fun i => n - (BinaryEdgePartition.active M i).card)) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    projectiveBandPartition hp hcap htpos hlam n htop
  have hold :
      ∀ i, (BinaryEdgePartition.active P i).card ≤
        (n + 1) - centreExponent (C i) t := by
    intro i
    dsimp [P]
    exact projectiveBandPartition_active_card_le_deficit
      hp hcap htpos hlam ht hdelta0 hdelta1 C i
  have hwrapP :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v := by
    simpa [P, htop] using hwrap
  apply BinaryEdgePartition.cluster_capacity_of_last_merge_weighted_repair
    hn P (fun i => centreExponent (C i) t)
    hold wrapBit hwrapP
  simpa [P, htop, hwrapP] using hrepair

#print axioms projectiveBand_capacity_of_last_merge_weighted_repair

end JSP000404Research
