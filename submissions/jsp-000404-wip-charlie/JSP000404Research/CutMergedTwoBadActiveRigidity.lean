import JSP000404Research.CutMergedTwoBadRigidity
import JSP000404Research.SixPointMergedTwoBadActiveSet
import Mathlib.Tactic

/-!
# Active-palette equality in the geometric two-bad cut

CutMergedTwoBadRigidity gives the root-colour factorization of the exact
two-bad branch.  The root is active at every minimum, and after erasing it the
five minima have cardinalities

  3,3,2,2,2.

Hence the full active profile is exactly

  1,4,4,3,3,3.

WeightedHanselSlice then forces the two exceptional 4-colour palettes to be
identical.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem uncovered_cut_two_bad_minima_active_eq
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
    active M bad₁ = active M bad₂ := by
  let M :=
    uncoveredCutMergedPartition
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered

  obtain ⟨_hSharp, root, hrootTop, hrootAll, _hrootEdges,
      hrootBad₁, hrootBad₂, hrootOther,
      _u₁, _u₂, _hu₁Centre, _hu₂Centre, _huNe,
      _hu₁Bad, _hu₂Bad⟩ :=
    uncovered_cut_two_bad_minima_rigidity
      hp hcap C (by omega : 4 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi hcard top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hTopExp hMinExp
      huncovered hTopSafe hBad₁ hBad₂ hOtherSafe

  have hTopCard :
      (active M top).card ≤ 1 := by
    rw [hrootTop]
    simp

  have hBad₁Mem :
      root ∈ active M bad₁ :=
    (hrootAll bad₁ htb₁.symm).1
  have hBad₂Mem :
      root ∈ active M bad₂ :=
    (hrootAll bad₂ htb₂.symm).1

  have hBad₁Card :
      (active M bad₁).card ≤ 4 := by
    have h := hrootBad₁
    rw [Finset.card_erase_of_mem hBad₁Mem] at h
    omega
  have hBad₂Card :
      (active M bad₂).card ≤ 4 := by
    have h := hrootBad₂
    rw [Finset.card_erase_of_mem hBad₂Mem] at h
    omega

  have hOtherCard :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active M v).card ≤ 3 := by
    intro v hvt hvb₁ hvb₂
    have hrootMem :
        root ∈ active M v :=
      (hrootAll v hvt).1
    have h := hrootOther v hvt hvb₁ hvb₂
    rw [Finset.card_erase_of_mem hrootMem] at h
    omega

  exact six_point_two_min_exceptions_active_eq
    hn5 M top bad₁ bad₂
    htb₁ htb₂ hb₁₂ hcard
    hTopCard hBad₁Card hBad₂Card hOtherCard

#print axioms uncovered_cut_two_bad_minima_active_eq

end JSP000404Research
