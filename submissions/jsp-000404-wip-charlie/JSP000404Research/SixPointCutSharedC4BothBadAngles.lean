import JSP000404Research.SixPointBadSharedC4FromEquality
import JSP000404Research.SixPointCutBothBadSmallAnglesDirect
import Mathlib.Tactic

/-!
# A shared C4 colour AND two real sub-lambda bad angles in the cut equality case

Package the certified five-minimum graph reduction and the independent
AngleCap-based cycle-neighbour-angle result under the SAME genuine
uncovered cut-merged partition. Both exceptional minima use the same
C4-bearing colour, and one of them actually lies on a cycle with a
sub-lambda angle to its cycle neighbours.

This is a rigorously local six-point terminal improvement. It neither
claims both exceptions lie on one four-cycle nor proves the global
actual-uncovered-hole nonreuse/payment inequality.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem six_point_cut_shared_C4_and_both_bad_small_angles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta c : ℝ}
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v) {n : ℕ}
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
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
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
    let M := uncoveredCutMergedPartition
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered
    (∃ colour : Fin n,
      colour ∈ active M bad₁ ∧
      colour ∈ active M bad₂ ∧
      HasFourCycle (localColourGraph M top colour)) ∧
    (∃ x y : V,
      x ≠ top ∧ x ≠ bad₁ ∧ y ≠ top ∧ y ≠ bad₁ ∧ x ≠ y ∧
      EuclideanGeometry.angle (p x) (p bad₁) (p y) < lam) ∧
    (∃ x y : V,
      x ≠ top ∧ x ≠ bad₂ ∧ y ≠ top ∧ y ≠ bad₂ ∧ x ≠ y ∧
      EuclideanGeometry.angle (p x) (p bad₂) (p y) < lam) := by
  dsimp only
  let M :=
    uncoveredCutMergedPartition hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf hc0 hcpi huncovered
  have hshared :=
    six_point_two_exception_shared_C4_active_at_both
      hn4 M top bad₁ bad₂ htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
  have hangle :=
    six_point_cut_both_bad_minima_have_strict_small_angles_direct
      hp hcap C hn4 htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered
      top bad₁ bad₂ htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther hbadCut₁ hbadCut₂
  exact ⟨hshared, hangle⟩

#print axioms six_point_cut_shared_C4_and_both_bad_small_angles

end JSP000404Research
