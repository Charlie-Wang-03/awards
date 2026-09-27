import JSP000404Research.CutMergedRepeatedSmallAngle
import Mathlib.Tactic

/-!
# Decoding equal uncovered merged colours back to old cut bands

At an uncovered cut the merged partition is obtained by the final 0/n colour
identification.  Therefore equality of two arbitrary local incident colours
in the merged partition has exactly three possible old-colour explanations:

* the old cut colours were equal;
* the first was 0 and the second n;
* the first was n and the second 0.

This cross-centre fibre bridge is the form needed by the remaining two-bad
support-three pair analysis.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem equal_uncovered_merged_incident_colors_old_fibre
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
    {i x j y : V}
    (heq :
      localIncidentColor
          (uncoveredCutMergedPartition
            hp hcap C hn htpos hlam ht hdelta0
            hdeltaHalf hc0 hcpi huncovered)
          i x
        =
      localIncidentColor
          (uncoveredCutMergedPartition
            hp hcap C hn htpos hlam ht hdelta0
            hdeltaHalf hc0 hcpi huncovered)
          j y) :
    let htop : t < (n + 1 : ℕ) := by
      rw [ht]; push_cast; linarith
    let P :=
      cutProjectiveBandPartition
        hp hcap htpos hlam hc0 hcpi n htop
    localIncidentColor P i x =
        localIncidentColor P j y
      ∨
    (localIncidentColor P i x = (0 : Fin (n + 1)) ∧
      localIncidentColor P j y = Fin.last n)
      ∨
    (localIncidentColor P i x = Fin.last n ∧
      localIncidentColor P j y = (0 : Fin (n + 1))) := by
  dsimp only
  have hmerge :
      mergeLastColor hn
          (localIncidentColor
            (cutProjectiveBandPartition
              hp hcap htpos hlam hc0 hcpi n
                (by rw [ht]; push_cast; linarith))
            i x)
        =
      mergeLastColor hn
          (localIncidentColor
            (cutProjectiveBandPartition
              hp hcap htpos hlam hc0 hcpi n
                (by rw [ht]; push_cast; linarith))
            j y) := by
    rw [← localIncidentColor_uncoveredCutMerged_eq_merge
        hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered i x,
      ← localIncidentColor_uncoveredCutMerged_eq_merge
        hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered j y]
    exact heq
  exact
    (mergeLastColor_eq_iff_eq_or_boundary_swap hn _ _).1
      hmerge

#print axioms equal_uncovered_merged_incident_colors_old_fibre

end JSP000404Research
