import JSP000404Research.FiveMinimaPendantRepeatedSmallAngle
import JSP000404Research.SixPointBadActiveC4
import JSP000404Research.CutMonochromaticC4Angles
import Mathlib.Tactic

/-!
# Every exceptional saturation-bad minimum has a non-top small angle

In the exact two-exception root-factorized terminal, each exceptional minimum
is active in some non-root colour whose five-minimum colour graph contains a
four-cycle.

Fix such a bad minimum b and such a colour c.

* If a c-coloured four-cycle contains b, the two cycle neighbours at b have
  genuine angle < lambda by CutMonochromaticC4Angles.
* If no c-coloured four-cycle contains b, the five-vertex bipartite graph
  forces b to be a pendant of the existing C4.  The other three incident
  minimum edges use only the other two reduced colours, so one repeats; the
  pendant repeated-colour theorem again gives a genuine angle < lambda.

Thus every saturation-bad exceptional minimum has a strict sub-lambda angle
between two other non-top vertices.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem exceptional_bad_has_nonTop_small_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ} {n : ℕ}
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

  obtain ⟨colour,hcolourRoot,hcolourBad,hC4⟩ :=
    bad_minimum_active_in_some_monochromatic_fourCycle
      M top bad₁ bad₂ root
      htb₁ htb₂ hb₁₂ hcard
      (by simpa [M] using hrootTop)
      (by simpa [M] using hrootEdges)
      (by simpa [M] using hBad₁)
      (by simpa [M] using hBad₂)
      (by simpa [M] using hOther)
      rootBad hbadCase

  have hbt : rootBad ≠ top := by
    rcases hbadCase with rfl | rfl
    · exact htb₁.symm
    · exact htb₂.symm

  let B : OtherVertex top := ⟨rootBad, hbt⟩

  by_cases hthrough :
      ∃ u v w : OtherVertex top,
        B ≠ u ∧ u ≠ v ∧ v ≠ w ∧ w ≠ B ∧
        B ≠ v ∧ u ≠ w ∧
        (localColourGraph M top colour).Adj B u ∧
        (localColourGraph M top colour).Adj u v ∧
        (localColourGraph M top colour).Adj v w ∧
        (localColourGraph M top colour).Adj w B
  · obtain ⟨u,v,w,hBu,huv,hvw,hwB,hBv,huw,
        hBuE,huvE,hvwE,hwBE⟩ := hthrough
    refine ⟨u.1,w.1,u.2,?_,w.2,?_,?_,?_⟩
    · intro h
      apply hBu
      apply Subtype.ext
      exact h.symm
    · intro h
      apply hwB
      apply Subtype.ext
      exact h
    · intro h
      apply huw
      apply Subtype.ext
      exact h
    · exact
        saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered top colour
          hBu hwB.symm huw
          hBuE hwBE hbadSat
  · have hReducedBad :
        ((active M rootBad).erase root).card = 3 := by
      rcases hbadCase with rfl | rfl
      · simpa [M] using hBad₁
      · simpa [M] using hBad₂
    exact
      pendant_saturation_bad_has_repeated_small_angle
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered
        top rootBad root colour hbt hcard
        (by simpa [M] using hrootTop)
        (by simpa [M] using hrootEdges)
        hcolourRoot hReducedBad
        (by simpa [M] using hcolourBad)
        (by simpa [M] using hC4)
        (by simpa [B,M] using hthrough)
        hbadSat

/-- Two-exception corollary: both saturation-bad minima carry their own
non-top strict sub-lambda angle witnesses. -/
theorem two_exception_bad_minima_each_have_small_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ} {n : ℕ}
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
