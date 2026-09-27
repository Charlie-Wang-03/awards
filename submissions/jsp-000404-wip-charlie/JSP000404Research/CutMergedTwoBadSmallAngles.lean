import JSP000404Research.CutMergedTwoBadRigidity
import JSP000404Research.CutMergedRepeatedSmallAngle
import Mathlib.Tactic

/-!
# Two bad minima each carry a genuine small non-top angle

Combine the exact two-bad root factorization with the 4-to-3 pigeonhole.

At either bad minimum b:

* the four edges from b to the other minima avoid the unique top root colour;
* after deleting the root, b has exactly three active merged colours;
* hence two distinct minimum--minimum edges have the same merged colour;
* because b is saturation-bad, colours 0 and n do not both occur in its old
  active palette, so mergeLastColor is injective there;
* the repeated merged colour therefore comes from one common old cut band;
* two distinct rays in one old cut band make a genuine angle < lambda.

Thus the remaining two-bad terminal carries two concrete small angles, one at
each bad minimum, and neither small-angle pair uses the sharp top.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem uncovered_cut_two_bad_minima_have_small_nonTop_angles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
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
    ∃ x₁ y₁ x₂ y₂ : V,
      x₁ ≠ top ∧ x₁ ≠ bad₁ ∧
      y₁ ≠ top ∧ y₁ ≠ bad₁ ∧
      x₁ ≠ y₁ ∧
      EuclideanGeometry.angle (p x₁) (p bad₁) (p y₁) < lam ∧
      x₂ ≠ top ∧ x₂ ≠ bad₂ ∧
      y₂ ≠ top ∧ y₂ ≠ bad₂ ∧
      x₂ ≠ y₂ ∧
      EuclideanGeometry.angle (p x₂) (p bad₂) (p y₂) < lam := by
  let M :=
    uncoveredCutMergedPartition
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered

  have hrig :=
    uncovered_cut_two_bad_minima_rigidity
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi hcard top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hTopExp hMinExp
      huncovered hTopSafe hBad₁ hBad₂ hOtherSafe
  dsimp only at hrig
  obtain ⟨_hSharp, root, _hrootTop, _hrootAll,
      hrootEdges, hrootBad₁, hrootBad₂,
      _hrootOther, _u₁, _u₂, _hu₁c, _hu₂c,
      _huNe, _hu₁Bad, _hu₂Bad⟩ := hrig

  obtain ⟨x₁, y₁, hx₁t, hx₁b, hy₁t, hy₁b,
      hx₁y₁, hmerge₁⟩ :=
    four_nonTop_edges_three_nonroot_colours_repeat
      M top bad₁ root htb₁.symm hcard
      hrootEdges hrootBad₁

  obtain ⟨x₂, y₂, hx₂t, hx₂b, hy₂t, hy₂b,
      hx₂y₂, hmerge₂⟩ :=
    four_nonTop_edges_three_nonroot_colours_repeat
      M top bad₂ root htb₂.symm hcard
      hrootEdges hrootBad₂

  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  let exponent : V → ℕ :=
    fun v => centreExponent (C v) t

  have hBad₁' :
      SaturationCollisionFailure P exponent bad₁ := by
    simpa [CutSaturationBadAt, P, exponent, htop] using hBad₁
  have hBad₂' :
      SaturationCollisionFailure P exponent bad₂ := by
    simpa [CutSaturationBadAt, P, exponent, htop] using hBad₂

  have hmergeOld₁ :
      mergeLastColor (by omega : 1 ≤ n)
          (localIncidentColor P bad₁ x₁)
        =
      mergeLastColor (by omega : 1 ≤ n)
          (localIncidentColor P bad₁ y₁) := by
    rw [← localIncidentColor_uncoveredCutMerged_eq_merge
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered bad₁ x₁,
        ← localIncidentColor_uncoveredCutMerged_eq_merge
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered bad₁ y₁]
    exact hmerge₁

  have hmergeOld₂ :
      mergeLastColor (by omega : 1 ≤ n)
          (localIncidentColor P bad₂ x₂)
        =
      mergeLastColor (by omega : 1 ≤ n)
          (localIncidentColor P bad₂ y₂) := by
    rw [← localIncidentColor_uncoveredCutMerged_eq_merge
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered bad₂ x₂,
        ← localIncidentColor_uncoveredCutMerged_eq_merge
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered bad₂ y₂]
    exact hmerge₂

  have holdEq₁ :
      localIncidentColor P bad₁ x₁ =
        localIncidentColor P bad₁ y₁ :=
    mergeLastColor_injOn_of_not_both_boundary
      (by omega : 1 ≤ n)
      (active P bad₁) hBad₁'.2
      (localIncidentColor_mem_active P hx₁b.symm)
      (localIncidentColor_mem_active P hy₁b.symm)
      hmergeOld₁

  have holdEq₂ :
      localIncidentColor P bad₂ x₂ =
        localIncidentColor P bad₂ y₂ :=
    mergeLastColor_injOn_of_not_both_boundary
      (by omega : 1 ≤ n)
      (active P bad₂) hBad₂'.2
      (localIncidentColor_mem_active P hx₂b.symm)
      (localIncidentColor_mem_active P hy₂b.symm)
      hmergeOld₂

  have hsmall₁ :
      EuclideanGeometry.angle (p x₁) (p bad₁) (p y₁) < lam := by
    exact actual_angle_lt_lam_of_equal_local_cut_color
      hp hcap htpos hlam hc0 hcpi n htop
      hx₁b.symm hy₁b.symm hx₁y₁
      (by simpa [P] using holdEq₁)

  have hsmall₂ :
      EuclideanGeometry.angle (p x₂) (p bad₂) (p y₂) < lam := by
    exact actual_angle_lt_lam_of_equal_local_cut_color
      hp hcap htpos hlam hc0 hcpi n htop
      hx₂b.symm hy₂b.symm hx₂y₂
      (by simpa [P] using holdEq₂)

  exact ⟨x₁, y₁, x₂, y₂,
    hx₁t, hx₁b, hy₁t, hy₁b, hx₁y₁, hsmall₁,
    hx₂t, hx₂b, hy₂t, hy₂b, hx₂y₂, hsmall₂⟩

#print axioms uncovered_cut_two_bad_minima_have_small_nonTop_angles

end JSP000404Research
