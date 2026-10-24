import JSP000404Research.SixPointMergedEqualityRoot
import JSP000404Research.SixPointMergedRepeatedColour
import JSP000404Research.CutMonochromaticC4Angles
import Mathlib.Tactic

/-!
# Two-bad six-point cut terminal: BOTH minima have actual small angles

No C4 selection, pendant classification, fifth-vertex enumeration, or
unverified edge-exclusion hypothesis is required here. Exact active-card
bounds imply the root factorization. At each exceptional minimum, four
non-top incident edges use three non-root merged colours, so a colour
repeats. The existing proved saturation-bad equal-colour angle lemma
then yields a genuine strict sub-lambda angle at THAT minimum.

This improves the on-C4-at-least-one-bad angle conclusion in the exact
six-point active-card terminal, but it does not prove global true-hole
nonreusing six-source payment.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem six_point_cut_both_bad_minima_have_strict_small_angles_direct
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
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop :
      (active (uncoveredCutMergedPartition
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered) top).card ≤ 1)
    (hBad₁ :
      (active (uncoveredCutMergedPartition
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered) bad₁).card ≤ 4)
    (hBad₂ :
      (active (uncoveredCutMergedPartition
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered) bad₂).card ≤ 4)
    (hOther :
      ∀ v : V, v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered) v).card ≤ 3)
    (hbadCut₁ :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi bad₁)
    (hbadCut₂ :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi bad₂) :
    (∃ x y : V,
      x ≠ top ∧ x ≠ bad₁ ∧
      y ≠ top ∧ y ≠ bad₁ ∧ x ≠ y ∧
      EuclideanGeometry.angle (p x) (p bad₁) (p y) < lam) ∧
    (∃ x y : V,
      x ≠ top ∧ x ≠ bad₂ ∧
      y ≠ top ∧ y ≠ bad₂ ∧ x ≠ y ∧
      EuclideanGeometry.angle (p x) (p bad₂) (p y) < lam) := by
  let M := uncoveredCutMergedPartition
    hp hcap C (by omega : 1 ≤ n)
    htpos hlam ht hdelta0 hdeltaHalf hc0 hcpi huncovered
  obtain ⟨root, _hrootTop, _hrootAll, hrootEdges,
      hredBad₁, hredBad₂, _hredOther⟩ :=
    six_point_two_exception_root_factorization
      hn4 M top bad₁ bad₂ htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
  have hrepeatAngle (bad : V) (hbt : bad ≠ top)
      (hred : ((active M bad).erase root).card = 3)
      (hbad : CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi bad) :
      ∃ x y : V,
        x ≠ top ∧ x ≠ bad ∧
        y ≠ top ∧ y ≠ bad ∧ x ≠ y ∧
        EuclideanGeometry.angle (p x) (p bad) (p y) < lam := by
    obtain ⟨x,y,hxt,hxb,hyt,hyb,hxy,heq⟩ :=
      four_nonTop_edges_three_nonroot_colours_repeat
        M top bad root hbt hcard hrootEdges hred
    refine ⟨x,y,hxt,hxb,hyt,hyb,hxy,?_⟩
    exact actual_angle_lt_lam_of_equal_uncovered_merged_color_at_saturation_bad
      hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered hxb.symm hyb.symm hxy hbad
      (by simpa [M] using heq)
  exact ⟨hrepeatAngle bad₁ htb₁.symm hredBad₁ hbadCut₁,
         hrepeatAngle bad₂ htb₂.symm hredBad₂ hbadCut₂⟩

#print axioms six_point_cut_both_bad_minima_have_strict_small_angles_direct

end JSP000404Research
