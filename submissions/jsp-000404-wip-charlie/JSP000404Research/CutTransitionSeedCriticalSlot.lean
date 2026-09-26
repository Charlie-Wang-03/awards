import JSP000404Research.CutAdjacentUnitGapBridge
import JSP000404Research.CyclicCriticalUnitPhase
import Mathlib.Tactic

/-!
# A short cut-transition seed produces a cyclic critical unit obstruction

Fix an arbitrary projective cut c.  Suppose two rays at one centre have
opposite cut-adjusted signs and both normalized cut coordinates lie in the
short interval [0,1+delta].

Refining the ordered pair inside the cut-sorted centre cycle gives a nested
adjacent transition of normalized length s with

  1 <= s <= 1+delta.

CutAdjacentUnitGapBridge returns the corresponding canonical q=1 slot and
the period-lift identity for its start.  Because the adjacent gap lies inside
the parent interval, its start beta satisfies

  0 <= beta,   beta+s <= 1+delta.

Consequently the global phase point

  t*c/pi + delta

lies in the critical interval of that canonical slot.
-/

namespace JSP000404Research

open Real

theorem ordered_cut_transition_seed_has_cyclic_critical_slot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (htheta :
      cutRayTheta hp c i j <
        cutRayTheta hp c i k)
    (hsign :
      cutRaySign hp c i j ≠
        cutRaySign hp c i k)
    (hjArc :
      0 ≤ cutNormalizedRayTheta hp t c i j ∧
      cutNormalizedRayTheta hp t c i j ≤ 1 + delta)
    (hkArc :
      0 ≤ cutNormalizedRayTheta hp t c i k ∧
      cutNormalizedRayTheta hp t c i k ≤ 1 + delta) :
    ∃ u : GlobalUnitGapSlot C t,
      u.1 = i ∧
      GlobalCyclicCriticalUnitBadAt
        C t delta u (t * c / Real.pi + delta) := by
  let R : CentreCutRayCycle hp (C i) c :=
    Classical.choice (exists_centreCutRayCycle hp (C i) c)

  obtain ⟨q, r, hsucc, hjLeQ, hrLeK,
      _htrans, hs1, hseedLe⟩ :=
    R.exists_adjacent_cut_transition_inside_ordered_seed
      hcap ht hlam hc0 hcpi htheta hsign

  have hseedTop :
      t * ((cutRayTheta hp c i k -
        cutRayTheta hp c i j) / Real.pi)
        ≤ 1 + delta := by
    have hcoord :
        cutNormalizedRayTheta hp t c i k -
            cutNormalizedRayTheta hp t c i j
          ≤ 1 + delta := by
      linarith [hjArc.1, hkArc.2]
    unfold cutNormalizedRayTheta at hcoord
    convert hcoord using 1 <;> ring

  have hsTop :
      t * ((cutRayTheta hp c i (R.rays.get r) -
        cutRayTheta hp c i (R.rays.get q)) / Real.pi)
        ≤ 1 + delta :=
    hseedLe.trans hseedTop

  let beta :=
    cutNormalizedRayTheta hp t c i (R.rays.get q)
  let s :=
    t * ((cutRayTheta hp c i (R.rays.get r) -
      cutRayTheta hp c i (R.rays.get q)) / Real.pi)

  have hbeta0 : 0 ≤ beta := by
    dsimp [beta]
    exact cutNormalizedRayTheta_nonneg
      hp ht.le hc0 hcpi i (R.rays.get q)

  have hthetaRK :
      cutRayTheta hp c i (R.rays.get r) ≤
        cutRayTheta hp c i k := by
    have h := R.cutTheta_le_of_rayIndex_le hrLeK
    simpa [R.get_rayIndex] using h

  have hcoordRK :
      cutNormalizedRayTheta hp t c i (R.rays.get r) ≤
        cutNormalizedRayTheta hp t c i k := by
    unfold cutNormalizedRayTheta
    have hpi : 0 < Real.pi := Real.pi_pos
    have hdiv :=
      div_le_div_of_nonneg_right hthetaRK hpi.le
    exact mul_le_mul_of_nonneg_left hdiv ht.le

  have hbetaAdd :
      beta + s =
        cutNormalizedRayTheta hp t c i (R.rays.get r) := by
    dsimp [beta, s, cutNormalizedRayTheta]
    ring

  have hbetaSTop : beta + s ≤ 1 + delta := by
    rw [hbetaAdd]
    exact hcoordRK.trans hkArc.2

  obtain ⟨uLocal, kShift, hstart⟩ :=
    exists_centreUnitGap_of_adjacent_cut_critical
      R ht hdeltaHalf hsucc hs1 hsTop

  let u : GlobalUnitGapSlot C t := ⟨i, uLocal⟩
  refine ⟨u, rfl, ?_⟩
  refine ⟨kShift, s, ?_, ?_, ?_, ?_⟩
  · exact hs1
  · exact hsTop
  · unfold criticalBadLeft
    have hstart' :
        globalUnitGapStart C t u + (kShift : ℝ) * t =
          t * c / Real.pi + beta := by
      simpa [u, beta] using hstart
    rw [hstart']
    linarith
  · unfold criticalBadRight
    have hstart' :
        globalUnitGapStart C t u + (kShift : ℝ) * t =
          t * c / Real.pi + beta := by
      simpa [u, beta] using hstart
    rw [hstart']
    linarith

/-- Orientation-free version. -/
theorem cut_transition_seed_has_cyclic_critical_slot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (i : V)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (hsign :
      cutRaySign hp c i j ≠
        cutRaySign hp c i k)
    (hjArc :
      0 ≤ cutNormalizedRayTheta hp t c i j ∧
      cutNormalizedRayTheta hp t c i j ≤ 1 + delta)
    (hkArc :
      0 ≤ cutNormalizedRayTheta hp t c i k ∧
      cutNormalizedRayTheta hp t c i k ≤ 1 + delta) :
    ∃ u : GlobalUnitGapSlot C t,
      u.1 = i ∧
      GlobalCyclicCriticalUnitBadAt
        C t delta u (t * c / Real.pi + delta) := by
  have hthetaNe :
      cutRayTheta hp c i j ≠
        cutRayTheta hp c i k := by
    intro heq
    have hcost :=
      one_le_t_mul_cutRay_gap_of_sign_ne
        hp hcap ht hlam hc0 hcpi i hjk
        (by rw [heq]) hsign
    rw [heq] at hcost
    norm_num at hcost
  rcases lt_or_gt_of_ne hthetaNe with hlt | hgt
  · exact ordered_cut_transition_seed_has_cyclic_critical_slot
      hp hcap C ht hlam hdeltaHalf hc0 hcpi
      i hjk hlt hsign hjArc hkArc
  · exact ordered_cut_transition_seed_has_cyclic_critical_slot
      hp hcap C ht hlam hdeltaHalf hc0 hcpi
      i hjk.symm hgt hsign.symm hkArc hjArc

#print axioms ordered_cut_transition_seed_has_cyclic_critical_slot
#print axioms cut_transition_seed_has_cyclic_critical_slot

end JSP000404Research
