import JSP000404Research.SixPointMergedRepeatedColour
import JSP000404Research.SixPointBadActiveC4
import JSP000404Research.CutMonochromaticC4Angles
import Mathlib.Tactic

/-!
# Each exceptional saturation-bad minimum has its own small angle

Uses a shorter proof than the earlier C4/pendant case split:
four non-top edges use three reduced colours, forcing a repeated incident
merged colour, and saturation-bad makes that a genuine strict sub-lambda
angle at the prescribed minimum. No C4 existence or pendant hypotheses
are needed.

Both individual and paired conclusions are sorry-free local consequences
of the genuine uncovered-cut setup, not a global true-hole payment.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem exceptional_bad_has_nonTop_small_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta c : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    (hn4 : 4 ≤ n)
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
    (top bad₁ bad₂ rootBad : V)
    (root : Fin n)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hrootTop :
      active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered)
        top = {root})
    (hrootEdges :
      ∀ {u v : V}, u < v →
        u ≠ top → v ≠ top →
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered).edgeColor u v ≠ root)
    (hBad₁ :
      ((active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered)
        bad₁).erase root).card = 3)
    (hBad₂ :
      ((active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered)
        bad₂).erase root).card = 3)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        ((active
          (uncoveredCutMergedPartition
            hp hcap C (by omega : 1 ≤ n)
            htpos hlam ht hdelta0 hdeltaHalf
            hc0 hcpi huncovered)
          v).erase root).card = 2)
    (hbadCase : rootBad = bad₁ ∨ rootBad = bad₂)
    (hbadSat :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi rootBad) :
    ∃ x y : V,
      x ≠ top ∧ x ≠ rootBad ∧
      y ≠ top ∧ y ≠ rootBad ∧
      x ≠ y ∧
      EuclideanGeometry.angle (p x) (p rootBad) (p y) < lam := by
  let M :=
    uncoveredCutMergedPartition
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered

  have hbt : rootBad ≠ top := by
    rcases hbadCase with h | h
    · rw [h]
      exact htb₁.symm
    · rw [h]
      exact htb₂.symm
  have hReducedBad :
      ((active M rootBad).erase root).card = 3 := by
    rcases hbadCase with h | h
    · rw [h]
      simpa only [M] using hBad₁
    · rw [h]
      simpa only [M] using hBad₂
  have hrootEdges' :
      ∀ {u v : V}, u < v →
        u ≠ top → v ≠ top → M.edgeColor u v ≠ root := by
    intro u v huv hut hvt
    exact hrootEdges huv hut hvt
  obtain ⟨x,y,hxt,hxb,hyt,hyb,hxy,heq⟩ :=
    four_nonTop_edges_three_nonroot_colours_repeat
      M top rootBad root hbt hcard hrootEdges' hReducedBad
  refine ⟨x,y,hxt,hxb,hyt,hyb,hxy,?_⟩
  exact actual_angle_lt_lam_of_equal_uncovered_merged_color_at_saturation_bad
    (i := rootBad) (x := x) (y := y)
    hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
    hc0 hcpi huncovered hxb.symm hyb.symm hxy hbadSat
    (by simpa only [M] using heq)
/-- Two-exception corollary: both saturation-bad minima carry their own
non-top strict sub-lambda angle witnesses. -/
theorem two_exception_bad_minima_each_have_small_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta c : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    (hn4 : 4 ≤ n)
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
    (top bad₁ bad₂ : V)
    (root : Fin n)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hrootTop :
      active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered)
        top = {root})
    (hrootEdges :
      ∀ {u v : V}, u < v →
        u ≠ top → v ≠ top →
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered).edgeColor u v ≠ root)
    (hBad₁ :
      ((active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered)
        bad₁).erase root).card = 3)
    (hBad₂ :
      ((active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered)
        bad₂).erase root).card = 3)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        ((active
          (uncoveredCutMergedPartition
            hp hcap C (by omega : 1 ≤ n)
            htpos hlam ht hdelta0 hdeltaHalf
            hc0 hcpi huncovered)
          v).erase root).card = 2)
    (hbad₁ :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi bad₁)
    (hbad₂ :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi bad₂) :
    (∃ x y : V,
      x ≠ top ∧ x ≠ bad₁ ∧
      y ≠ top ∧ y ≠ bad₁ ∧
      x ≠ y ∧
      EuclideanGeometry.angle (p x) (p bad₁) (p y) < lam)
    ∧
    (∃ x y : V,
      x ≠ top ∧ x ≠ bad₂ ∧
      y ≠ top ∧ y ≠ bad₂ ∧
      x ≠ y ∧
      EuclideanGeometry.angle (p x) (p bad₂) (p y) < lam) := by
  constructor
  · exact exceptional_bad_has_nonTop_small_angle
      hp hcap C hn4 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered
      top bad₁ bad₂ bad₁ root
      htb₁ htb₂ hb₁₂ hcard
      hrootTop hrootEdges hBad₁ hBad₂ hOther
      (Or.inl rfl) hbad₁
  · exact exceptional_bad_has_nonTop_small_angle
      hp hcap C hn4 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered
      top bad₁ bad₂ bad₂ root
      htb₁ htb₂ hb₁₂ hcard
      hrootTop hrootEdges hBad₁ hBad₂ hOther
      (Or.inr rfl) hbad₂

#print axioms exceptional_bad_has_nonTop_small_angle
#print axioms two_exception_bad_minima_each_have_small_angle

end JSP000404Research
