import JSP000404Research.SixPointOrdinaryInsideBadPalette
import JSP000404Research.CutMergedTwoBadRigidity
import Mathlib.Tactic

/-!
# Geometric wrapper for the ordinary-inside-common-palette witness

At a critical-uncovered cut with sharp top safe and exactly two saturation-bad
minima, the merged partition has the exact two-exception Hansel profile.

The abstract equality theorem SixPointOrdinaryInsideBadPalette therefore
supplies a third ordinary minimum whose two non-root active colours are
contained in the common reduced palette of the two bad minima.

This is the cut-geometric entry point for the remaining endpoint-incidence
argument.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem uncovered_cut_two_bad_has_ordinary_inside_common_palette
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (hcard : Fintype.card V = 6)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hTopExp :
      centreExponent (C top) t = n - 1)
    (hMinExp :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi))
    (hTopSafe :
      ¬ CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi top)
    (hBad₁ :
      CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi bad₁)
    (hBad₂ :
      CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi bad₂)
    (hOtherSafe :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        ¬ CutSaturationBadAt
            hp hcap C htpos hlam ht hdelta0
            (by linarith : delta < 1)
            hc0 hcpi v) :
    let M :=
      uncoveredCutMergedPartition
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered
    ∃ root : Fin n, ∃ v : V,
      v ≠ top ∧ v ≠ bad₁ ∧ v ≠ bad₂ ∧
      ((active M v).erase root) ⊆
        ((active M bad₁).erase root) := by
  let M :=
    uncoveredCutMergedPartition
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered

  have hTopActive :
      (active M top).card ≤ 1 := by
    have h :=
      uncoveredCutMergedPartition_active_le_of_not_bad
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered top hTopSafe
    rw [hTopExp] at h
    simpa [M] using (show
      (active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered)
        top).card ≤ 1 by omega)

  have hBad₁Active :
      (active M bad₁).card ≤ 4 := by
    have h :=
      uncoveredCutMergedPartition_active_le_one_extra
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered bad₁
    rw [hMinExp bad₁ htb₁.symm] at h
    simpa [M] using (show
      (active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered)
        bad₁).card ≤ 4 by omega)

  have hBad₂Active :
      (active M bad₂).card ≤ 4 := by
    have h :=
      uncoveredCutMergedPartition_active_le_one_extra
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered bad₂
    rw [hMinExp bad₂ htb₂.symm] at h
    simpa [M] using (show
      (active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered)
        bad₂).card ≤ 4 by omega)

  have hOtherActive :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active M v).card ≤ 3 := by
    intro v hvt hvb₁ hvb₂
    have h :=
      uncoveredCutMergedPartition_active_le_of_not_bad
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered v
        (hOtherSafe v hvt hvb₁ hvb₂)
    rw [hMinExp v hvt] at h
    simpa [M] using (show
      (active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered)
        v).card ≤ 3 by omega)

  exact exists_ordinary_reduced_active_subset_bad
    hn5 M top bad₁ bad₂
    htb₁ htb₂ hb₁₂ hcard
    hTopActive hBad₁Active hBad₂Active hOtherActive

#print axioms uncovered_cut_two_bad_has_ordinary_inside_common_palette

end JSP000404Research
