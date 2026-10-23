import JSP000404Research.CutAdjacentUnitGapBridge
import JSP000404Research.CyclicCriticalUnitPhase
import Mathlib.Tactic

/-!
# Exact cut-adjacent critical interval to canonical cyclic bad-phase bridge

A cut-dependent adjacent critical transition belongs to an ORIGINAL
centre's canonical cyclic q=1 slot, and its cut-normalized beginning
agrees with a canonical slot start up to an integral t-period shift.

This theorem transports BOTH bad-phase inequalities to the canonical
periodic critical predicate at the SAME real phase x. It preserves the
actual gap scaled length s. This bridge includes ordinary and wrap
adjacency, without a new phase-cover or Boolean-hole payment hypothesis.

The separate geometric task "every surviving merged-wrap triangle yields
one such adjacent critical gap" and the global six-source Boolean-hole
allocation are NOT solved by this theorem.
-/

namespace JSP000404Research

theorem cut_adjacent_critical_bad_implies_cyclic_unit_bad
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (i : V) (c : ℝ)
    (R : CentreCutRayCycle hp (C i) c)
    {t delta x : ℝ}
    (ht : 0 < t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    {q r : Fin R.rays.length}
    (hsucc : r.val = q.val + 1)
    (hs1 :
      1 ≤ t * ((cutRayTheta hp c i (R.rays.get r) -
        cutRayTheta hp c i (R.rays.get q)) / Real.pi))
    (hsTop :
      t * ((cutRayTheta hp c i (R.rays.get r) -
        cutRayTheta hp c i (R.rays.get q)) / Real.pi)
          ≤ 1 + delta)
    (hx :
      let alpha :=
        t * c / Real.pi +
          cutNormalizedRayTheta hp t c i (R.rays.get q)
      let s :=
        t * ((cutRayTheta hp c i (R.rays.get r) -
          cutRayTheta hp c i (R.rays.get q)) / Real.pi)
      criticalBadLeft alpha s ≤ x ∧
        x ≤ criticalBadRight alpha delta) :
    ∃ u : GlobalUnitGapSlot C t,
      u.1 = i ∧ GlobalCyclicCriticalUnitBadAt C t delta u x := by
  obtain ⟨v, k, hk⟩ :=
    exists_centreUnitGap_of_adjacent_cut_critical
      R ht hdeltaHalf hsucc hs1 hsTop
  let u : GlobalUnitGapSlot C t := ⟨i, v⟩
  let s : ℝ :=
    t * ((cutRayTheta hp c i (R.rays.get r) -
      cutRayTheta hp c i (R.rays.get q)) / Real.pi)
  let alpha : ℝ :=
    t * c / Real.pi +
      cutNormalizedRayTheta hp t c i (R.rays.get q)
  have hstart :
      globalUnitGapStart C t u + (k : ℝ) * t = alpha := by
    simpa only [globalUnitGapStart, u, alpha] using hk
  have hxL : criticalBadLeft alpha s ≤ x := hx.1
  have hxR : x ≤ criticalBadRight alpha delta := hx.2
  refine ⟨u, rfl, ?_⟩
  change ∃ k' : ℤ, ∃ s' : ℝ,
    let alpha' := globalUnitGapStart C t u + (k' : ℝ) * t
    1 ≤ s' ∧ s' ≤ 1 + delta ∧
      criticalBadLeft alpha' s' ≤ x ∧
      x ≤ criticalBadRight alpha' delta
  refine ⟨k, s, ?_, ?_, ?_, ?_⟩
  · exact hs1
  · exact hsTop
  · change criticalBadLeft
        (globalUnitGapStart C t u + (k : ℝ) * t) s ≤ x
    rw [hstart]
    exact hxL
  · change x ≤ criticalBadRight
        (globalUnitGapStart C t u + (k : ℝ) * t) delta
    rw [hstart]
    exact hxR

#print axioms cut_adjacent_critical_bad_implies_cyclic_unit_bad

end JSP000404Research
