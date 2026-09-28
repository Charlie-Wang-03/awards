import JSP000404Research.CutMergedSameColourSmallAngle
import JSP000404Research.SixPointMergedMonochromaticC4
import JSP000404Research.CutMergedOneExceptionTerminal
import Mathlib.Tactic

/-!
# Monochromatic C4 angles at saturation-bad vertices

At a critical-uncovered cut, equal merged incident colours only imply the
uniform bound (1+delta)*lambda in general, because the common merged colour
may identify old boundary bands 0 and n.

At a saturation-bad centre, however, the defining collision failure says
that old boundary colours 0 and n are not both active there.  Therefore
mergeLastColor is injective on that centre's active palette.  Equal merged
incident colours lift back to equal old cut colours, hence the two rays lie in
one old cut unit band and their genuine angle is strictly below lambda.

Applied to a monochromatic four-cycle among the five minima, every cycle
vertex which is itself saturation-bad therefore carries a strict <lambda
angle between its two cycle neighbours.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem actual_angle_lt_lam_of_equal_uncovered_merged_color_at_saturation_bad
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
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
    {i x y : V}
    (hix : i ≠ x)
    (hiy : i ≠ y)
    (hxy : x ≠ y)
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi i)
    (heq :
      localIncidentColor
          (uncoveredCutMergedPartition
            hp hcap C hn htpos hlam ht
            hdelta0 hdeltaHalf hc0 hcpi huncovered)
          i x
        =
      localIncidentColor
          (uncoveredCutMergedPartition
            hp hcap C hn htpos hlam ht
            hdelta0 hdeltaHalf hc0 hcpi huncovered)
          i y) :
    EuclideanGeometry.angle (p x) (p i) (p y) < lam := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  let wrapBit :=
    cutBoundaryWrapBit hp n htpos htop hc0 hcpi
  have hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v := by
    simpa [P, wrapBit] using
      cutBoundaryWrapBit_separates
        hp hcap C hn htpos hlam ht
        hdelta0 hdeltaHalf hc0 hcpi huncovered
  have hbad' :
      SaturationCollisionFailure
        P (fun v => centreExponent (C v) t) i := by
    simpa [CutSaturationBadAt, P, htop] using hbad
  have hboundary :
      ¬ ((0 : Fin (n + 1)) ∈ active P i ∧
        Fin.last n ∈ active P i) :=
    hbad'.2
  have heqMerge :
      localIncidentColor
          (mergeLastPartition hn P wrapBit hwrap) i x
        =
      localIncidentColor
          (mergeLastPartition hn P wrapBit hwrap) i y := by
    have hx :=
      localIncidentColor_uncoveredCutMerged_eq_merge
        hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered i x
    have hy :=
      localIncidentColor_uncoveredCutMerged_eq_merge
        hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered i y
    rw [hx, hy]
    simpa [P, wrapBit] using heq
  have hold :
      localIncidentColor P i x =
        localIncidentColor P i y :=
    old_localIncidentColor_eq_of_merged_eq_of_boundary_failure
      hn P wrapBit hwrap i x y hix hiy hboundary heqMerge
  exact actual_angle_lt_lam_of_equal_local_cut_color
    hp hcap htpos hlam hc0 hcpi n htop
    hix hiy hxy (by simpa [P] using hold)

/-- One saturation-bad vertex on a monochromatic four-cycle has a strict
sub-lambda angle between its two cycle neighbours. -/
theorem saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
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
    (top : V)
    (colour : Fin n)
    {a b d : OtherVertex top}
    (hab : a ≠ b)
    (had : a ≠ d)
    (hbd : b ≠ d)
    (habEdge :
      (localColourGraph
        (uncoveredCutMergedPartition
          hp hcap C hn htpos hlam ht
          hdelta0 hdeltaHalf hc0 hcpi huncovered)
        top colour).Adj a b)
    (hdaEdge :
      (localColourGraph
        (uncoveredCutMergedPartition
          hp hcap C hn htpos hlam ht
          hdelta0 hdeltaHalf hc0 hcpi huncovered)
        top colour).Adj d a)
    (hbadA :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi a.1) :
    EuclideanGeometry.angle (p b.1) (p a.1) (p d.1) < lam := by
  let M :=
    uncoveredCutMergedPartition
      hp hcap C hn htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi huncovered
  have habData :=
    (localColourGraph_adj M top colour a b).1 habEdge
  have hdaData :=
    (localColourGraph_adj M top colour d a).1 hdaEdge
  have hadColour :
      localIncidentColor M a.1 d.1 = colour := by
    rw [localIncidentColor_comm M]
    exact hdaData.2
  have heq :
      localIncidentColor M a.1 b.1 =
        localIncidentColor M a.1 d.1 := by
    rw [habData.2, hadColour]
  exact
    actual_angle_lt_lam_of_equal_uncovered_merged_color_at_saturation_bad
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered
      a.1 b.1 d.1
      (by
        intro h
        exact hab (Subtype.ext h))
      (by
        intro h
        exact had (Subtype.ext h))
      (by
        intro h
        exact hbd (Subtype.ext h))
      hbadA
      (by simpa [M] using heq)

#print axioms actual_angle_lt_lam_of_equal_uncovered_merged_color_at_saturation_bad
#print axioms saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle

end JSP000404Research
