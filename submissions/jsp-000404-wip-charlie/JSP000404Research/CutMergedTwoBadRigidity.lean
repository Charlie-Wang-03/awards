import JSP000404Research.CutSaturationGlobalTurnSlot
import JSP000404Research.SixPointMergedEqualityRoot
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

/-!
# Rigidity of a cut with exactly two bad minima

The one-exception terminal already rules out an uncovered cut at which the top
is safe and at most one minimum is saturation-bad.  The next critical branch
is therefore exactly two bad minima.

At such a cut:

* the top exponent n-1 makes the top geometrically SharpAt;
* the merged n-colour partition has exact active profile
      1,4,4,3,3,3;
* the unique top colour is a root colour incident to every minimum;
* all minimum--minimum edges avoid that root colour;
* after erasing the root colour the five minima have exact profile
      3,3,2,2,2;
* each bad minimum is witnessed at the same phase by a canonical global
  turn-unit slot, and the two slots are distinct because their centre
  components are distinct.

This file packages the complete equality-side interface for the remaining
two-bad-minimum geometry.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem uncovered_cut_two_bad_minima_rigidity
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
    let M :=
      uncoveredCutMergedPartition
        hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf
        hc0 hcpi huncovered
    SharpAt p delta lam top ∧
      ∃ root : Fin n,
        active M top = {root} ∧
        (∀ v : V, v ≠ top →
          root ∈ active M v ∧
          M.bit v root ≠ M.bit top root) ∧
        (∀ {u v : V}, u < v →
          u ≠ top → v ≠ top →
          M.edgeColor u v ≠ root) ∧
        ((active M bad₁).erase root).card = 3 ∧
        ((active M bad₂).erase root).card = 3 ∧
        (∀ v : V,
          v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
          ((active M v).erase root).card = 2) ∧
        ∃ u₁ u₂ : GlobalTurnUnitSlot C t,
          u₁.1 = bad₁ ∧
          u₂.1 = bad₂ ∧
          u₁ ≠ u₂ ∧
          GlobalCyclicTurnUnitBadAt
            C t delta u₁ (t * c / Real.pi) ∧
          GlobalCyclicTurnUnitBadAt
            C t delta u₂ (t * c / Real.pi) := by
  let M :=
    uncoveredCutMergedPartition
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered

  have hSharp :
      SharpAt p delta lam top := by
    exact concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 (by linarith : delta < 1)
      ht hlam top (C top) hTopExp

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
    have hExp :
        centreExponent (C bad₁) t = n - 3 :=
      hMinExp bad₁ htb₁.symm
    rw [hExp] at h
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
    have hExp :
        centreExponent (C bad₂) t = n - 3 :=
      hMinExp bad₂ htb₂.symm
    rw [hExp] at h
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

  obtain ⟨root, hrootTop, hrootAll, hrootEdges,
      hrootBad₁, hrootBad₂, hrootOther⟩ :=
    six_point_two_exception_root_factorization
      hn M top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTopActive hBad₁Active hBad₂Active hOtherActive

  obtain ⟨u₁, hu₁Centre, hu₁Bad⟩ :=
    cutSaturationBadAt_has_global_turnUnit_bad
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi bad₁ hBad₁
  obtain ⟨u₂, hu₂Centre, hu₂Bad⟩ :=
    cutSaturationBadAt_has_global_turnUnit_bad
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi bad₂ hBad₂

  have huNe : u₁ ≠ u₂ := by
    intro hEq
    have hfirst := congrArg Sigma.fst hEq
    rw [hu₁Centre, hu₂Centre] at hfirst
    exact hb₁₂ hfirst

  exact ⟨hSharp, root, hrootTop, hrootAll, hrootEdges,
    hrootBad₁, hrootBad₂, hrootOther,
    u₁, u₂, hu₁Centre, hu₂Centre, huNe,
    hu₁Bad, hu₂Bad⟩

#print axioms uncovered_cut_two_bad_minima_rigidity

end JSP000404Research
