import JSP000404Research.CutMergedTwoBadActiveRigidity
import JSP000404Research.MergeLastPalettePullback
import Mathlib.Tactic

/-!
# Pull back the two-bad merged-palette equality to the old cut bands

At the geometric two-bad equality cut, the two bad minima have identical
active palettes after the final 0/n merge.

Each bad minimum is, by definition, a saturation collision failure: its old
palette does not contain both boundary colours 0 and n.  On such a palette
mergeLastColor is injective.  Hence the equality of merged palettes determines
the old palettes up to the unique global ambiguity of mergeLastColor:

  old 0  ~  old n.

Consequently:

* every interior band 1,...,n-1 is active at bad1 iff it is active at bad2;
* either the two old palettes are identical, or one is obtained from the
  other by replacing 0 with n.

This is the numerical-band interface needed for the remaining two-centre
geometry.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem uncovered_cut_two_bad_old_palettes_differ_only_boundary
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
    let htop : t < (n + 1 : ℕ) := by
      rw [ht]
      push_cast
      linarith
    let P :=
      cutProjectiveBandPartition
        hp hcap htpos hlam hc0 hcpi n htop
    let S := active P bad₁
    let T := active P bad₂
    (∀ a : Fin (n + 1),
      0 < a.val → a.val < n →
      (a ∈ S ↔ a ∈ T))
      ∧
    (((0 : Fin (n + 1)) ∈ S ∨ Fin.last n ∈ S)
      ↔
     ((0 : Fin (n + 1)) ∈ T ∨ Fin.last n ∈ T))
      ∧
    (
      S = T
      ∨
      (
        (0 : Fin (n + 1)) ∈ S ∧
        Fin.last n ∉ S ∧
        (0 : Fin (n + 1)) ∉ T ∧
        Fin.last n ∈ T
      )
      ∨
      (
        (0 : Fin (n + 1)) ∉ S ∧
        Fin.last n ∈ S ∧
        (0 : Fin (n + 1)) ∈ T ∧
        Fin.last n ∉ T
      )
    ) := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  let exponent : V → ℕ :=
    fun i => centreExponent (C i) t
  let wrapBit :=
    cutBoundaryWrapBit hp n htpos htop hc0 hcpi
  have hwrap :
      ∀ {u v : V}, u < v →
        ((P.edgeColor u v).val = 0 ∨
          (P.edgeColor u v).val = n) →
        wrapBit u ≠ wrapBit v := by
    simpa [P, wrapBit, htop] using
      cutBoundaryWrapBit_separates
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered

  let M :=
    uncoveredCutMergedPartition
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered

  have hMergedEq :
      active M bad₁ = active M bad₂ :=
    uncovered_cut_two_bad_minima_active_eq
      hp hcap C hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi hcard
      top bad₁ bad₂ htb₁ htb₂ hb₁₂
      hTopExp hMinExp huncovered
      hTopSafe hBad₁ hBad₂ hOtherSafe

  have hMergedEq' :
      active
          (mergeLastPartition
            (by omega : 1 ≤ n) P wrapBit hwrap)
          bad₁
        =
      active
          (mergeLastPartition
            (by omega : 1 ≤ n) P wrapBit hwrap)
          bad₂ := by
    simpa [M, uncoveredCutMergedPartition,
      P, exponent, wrapBit, htop, hwrap] using hMergedEq

  have hImageEq :
      (active P bad₁).image
          (mergeLastColor (by omega : 1 ≤ n))
        =
      (active P bad₂).image
          (mergeLastColor (by omega : 1 ≤ n)) := by
    rw [mergeLastPartition_active_eq_image
          (by omega : 1 ≤ n) P wrapBit hwrap bad₁,
        mergeLastPartition_active_eq_image
          (by omega : 1 ≤ n) P wrapBit hwrap bad₂]
        at hMergedEq'
    exact hMergedEq'

  have hBad₁' :
      SaturationCollisionFailure P exponent bad₁ := by
    simpa [CutSaturationBadAt, P, exponent, htop] using hBad₁
  have hBad₂' :
      SaturationCollisionFailure P exponent bad₂ := by
    simpa [CutSaturationBadAt, P, exponent, htop] using hBad₂

  exact equal_merge_image_old_palettes_differ_only_boundary
    (by omega : 1 ≤ n)
    (active P bad₁) (active P bad₂)
    hBad₁'.2 hBad₂'.2 hImageEq

#print axioms uncovered_cut_two_bad_old_palettes_differ_only_boundary

end JSP000404Research
