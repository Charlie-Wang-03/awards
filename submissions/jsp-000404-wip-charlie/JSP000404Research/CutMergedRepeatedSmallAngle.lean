import JSP000404Research.SixPointMergedRepeatedColour
import JSP000404Research.LastMergeActiveExact
import JSP000404Research.CutBandSmallAngle
import Mathlib.Tactic

/-!
# Lifting repeated merged colours back to old cut bands

At a centre where the last 0/n merge does not collide, mergeLastColor is
injective on the old active palette.  Hence equal merged incident colours
come from equal old incident colours.

For cutProjectiveBandPartition the undirected local incident colour is exactly
the cut band of the ray from the centre to the neighbour.  Equal old incident
colours therefore give two rays in the same cut unit band, hence a genuine
angle strictly below lambda.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem localIncidentColor_mergeLastPartition
    {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (i j : V) :
    localIncidentColor
        (mergeLastPartition hn P wrapBit hwrap) i j
      =
    mergeLastColor hn (localIncidentColor P i j) := by
  unfold localIncidentColor mergeLastPartition
  split_ifs <;> rfl

theorem old_localIncidentColor_eq_of_merged_eq_of_boundary_failure
    {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n)
    (P : BinaryEdgePartition V (n + 1))
    (wrapBit : V → Bool)
    (hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v)
    (i x y : V)
    (hix : i ≠ x)
    (hiy : i ≠ y)
    (hboundary :
      ¬ ((0 : Fin (n + 1)) ∈ active P i ∧
         Fin.last n ∈ active P i))
    (heq :
      localIncidentColor
          (mergeLastPartition hn P wrapBit hwrap) i x
        =
      localIncidentColor
          (mergeLastPartition hn P wrapBit hwrap) i y) :
    localIncidentColor P i x =
      localIncidentColor P i y := by
  have hmerge :
      mergeLastColor hn (localIncidentColor P i x) =
        mergeLastColor hn (localIncidentColor P i y) := by
    rw [← localIncidentColor_mergeLastPartition,
        ← localIncidentColor_mergeLastPartition]
    exact heq
  exact
    mergeLastColor_injOn_of_not_both_boundary
      hn (active P i) hboundary
      (localIncidentColor_mem_active P hix)
      (localIncidentColor_mem_active P hiy)
      hmerge

theorem localIncidentColor_cutProjective_eq
    {V : Type*} [LinearOrder V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {i j : V}
    (hij : i ≠ j) :
    localIncidentColor
      (cutProjectiveBandPartition
        hp hcap ht hlam hc0 hcpi n htop)
      i j
      =
    cutProjectiveBandColor hp ht hc0 hcpi n htop i j := by
  unfold localIncidentColor cutProjectiveBandPartition
  by_cases hlt : i < j
  · rw [dif_pos hlt]
  · rw [dif_neg hlt]
    exact
      (cutProjectiveBandColor_symm
        hp ht hc0 hcpi n htop hij).symm

theorem actual_angle_lt_lam_of_equal_local_cut_color
    {V : Type*} [LinearOrder V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {i x y : V}
    (hix : i ≠ x)
    (hiy : i ≠ y)
    (hxy : x ≠ y)
    (heq :
      localIncidentColor
          (cutProjectiveBandPartition
            hp hcap ht hlam hc0 hcpi n htop)
          i x
        =
      localIncidentColor
          (cutProjectiveBandPartition
            hp hcap ht hlam hc0 hcpi n htop)
          i y) :
    EuclideanGeometry.angle (p x) (p i) (p y) < lam := by
  let xo : OtherVertex i := ⟨x, hix.symm⟩
  let yo : OtherVertex i := ⟨y, hiy.symm⟩
  let b :=
    cutProjectiveBandColor hp ht hc0 hcpi n htop i x
  have hbandEq :
      cutProjectiveBandColor hp ht hc0 hcpi n htop i x =
        cutProjectiveBandColor hp ht hc0 hcpi n htop i y := by
    rw [← localIncidentColor_cutProjective_eq
          hp hcap ht hlam hc0 hcpi n htop hix,
        ← localIncidentColor_cutProjective_eq
          hp hcap ht hlam hc0 hcpi n htop hiy]
    exact heq
  have hxBand :
      RayInCutProjectiveBand hp t c i xo b := by
    dsimp [xo, b]
    exact cutProjectiveBandColor_mem_lower
      hp ht hc0 hcpi n htop hix
  have hyBand :
      RayInCutProjectiveBand hp t c i yo b := by
    dsimp [yo, b]
    have h :=
      cutProjectiveBandColor_mem_lower
        hp ht hc0 hcpi n htop hiy
    rw [← hbandEq] at h
    exact h
  have hxoYo : xo ≠ yo := by
    intro h
    apply hxy
    exact congrArg Subtype.val h
  exact actual_angle_lt_lam_of_same_cut_band
    hp hcap ht hlam hc0 hcpi i xo yo hxoYo
    hxBand.1 hxBand.2 hyBand.1 hyBand.2

theorem localIncidentColor_uncoveredCutMerged_eq_merge
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
          C t delta u (t * c / Real.pi))
    (i j : V) :
    let htop : t < (n + 1 : ℕ) := by
      rw [ht]; push_cast; linarith
    let P :=
      cutProjectiveBandPartition
        hp hcap htpos hlam hc0 hcpi n htop
    localIncidentColor
        (uncoveredCutMergedPartition
          hp hcap C hn htpos hlam ht hdelta0
          hdeltaHalf hc0 hcpi huncovered)
        i j
      =
    mergeLastColor hn (localIncidentColor P i j) := by
  dsimp only
  unfold uncoveredCutMergedPartition
  dsimp only
  exact localIncidentColor_mergeLastPartition
    hn
    (cutProjectiveBandPartition hp hcap htpos hlam
      hc0 hcpi n
      (by rw [ht]; push_cast; linarith))
    (cutBoundaryWrapBit hp n htpos
      (by rw [ht]; push_cast; linarith) hc0 hcpi)
    (by
      simpa using
        cutBoundaryWrapBit_separates
          hp hcap C hn htpos hlam ht hdelta0
          hdeltaHalf hc0 hcpi huncovered)
    i j

#print axioms localIncidentColor_mergeLastPartition
#print axioms old_localIncidentColor_eq_of_merged_eq_of_boundary_failure
#print axioms localIncidentColor_cutProjective_eq
#print axioms actual_angle_lt_lam_of_equal_local_cut_color

end JSP000404Research
