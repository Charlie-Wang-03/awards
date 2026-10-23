import JSP000404Research.CutCriticalToCyclicBadPhase
import JSP000404Research.CyclicCriticalUnitPhase
import Mathlib.Tactic

/-!
# One of eleven phase samples avoids EVERY cut-adjacent critical obstruction

This is a quantified original-centre/cut-order result, not an abstract
finite phase-cover assumption. A bad phase may be certified by ANY centre,
ANY cut, ANY sorted cut ray cycle, and either ordinary or wrap adjacency.
The adjacent scaled gap must genuinely lie in [1,1+delta], and the phase
must lie in the actual associated bad interval. The cut-to-canonical
bridge makes that a periodic canonical q=1 bad slot; the eleven-sample
theorem rules out covering all samples using only ten slots.

The missing geometric link remains: establishing that every possible
failure of the DYADIC Boolean-hole payment necessarily yields such an
adjacent cut-critical certificate. In particular this theorem does NOT
rule out hard/soft/twin/mixed-rigid sources in general.
-/

namespace JSP000404Research

/-- A concrete bad-phase certificate carried by an adjacent pair in a
centre's cut-ordered projective ray list (the cut is not fixed). -/
def ExistsCutAdjacentCriticalBadAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t delta x : ℝ) : Prop :=
  ∃ i : V, ∃ c : ℝ,
    ∃ R : CentreCutRayCycle hp (C i) c,
    ∃ q r : Fin R.rays.length,
      r.val = q.val + 1 ∧
      (1 ≤ t * ((cutRayTheta hp c i (R.rays.get r) -
        cutRayTheta hp c i (R.rays.get q)) / Real.pi)) ∧
      (t * ((cutRayTheta hp c i (R.rays.get r) -
        cutRayTheta hp c i (R.rays.get q)) / Real.pi) ≤ 1 + delta) ∧
      (let alpha :=
         t * c / Real.pi +
           cutNormalizedRayTheta hp t c i (R.rays.get q)
       let s :=
         t * ((cutRayTheta hp c i (R.rays.get r) -
           cutRayTheta hp c i (R.rays.get q)) / Real.pi)
       criticalBadLeft alpha s ≤ x ∧
         x ≤ criticalBadRight alpha delta)

/-- Every concrete cut-adjacent critical bad phase, including cut-wrap
adjacency, is accounted for by ONE canonical periodic unit-gap slot. -/
theorem cutCriticalBadAt_implies_cyclicUnitBadAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta x : ℝ}
    (htpos : 0 < t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hbad : ExistsCutAdjacentCriticalBadAt C t delta x) :
    ∃ u : GlobalUnitGapSlot C t,
      GlobalCyclicCriticalUnitBadAt C t delta u x := by
  obtain ⟨i, c, R, q, r, hsucc, hs1, hsTop, hx⟩ := hbad
  obtain ⟨u, _, huBad⟩ :=
    cut_adjacent_critical_bad_implies_cyclic_unit_bad
      C i c R htpos hdeltaHalf hsucc hs1 hsTop hx
  exact ⟨u, huBad⟩

/-- An unconditional finite-sample avoidance theorem for the ACTUAL
cut-adjacent critical events, for n>=5 and 0<=delta<1/2.

No arbitrary cover-lower-bound premise and no full-real-line cover
assumption occurs anywhere in the statement. -/
theorem six_point_exists_elevenPhase_without_cut_critical
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3) :
    ∃ r : Fin 11,
      ¬ ExistsCutAdjacentCriticalBadAt C t delta (elevenPhase t r) := by
  obtain ⟨r, hr⟩ :=
    exists_uncovered_elevenPhase_of_six_point_terminal
      C hn4 hn5 hdelta0 hdeltaHalf ht
      hcard top hTop hMin
  refine ⟨r, ?_⟩
  intro hbad
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  obtain ⟨u, hu⟩ :=
    cutCriticalBadAt_implies_cyclicUnitBadAt
      C htpos hdeltaHalf hbad
  exact hr u hu

#print axioms cutCriticalBadAt_implies_cyclicUnitBadAt
#print axioms six_point_exists_elevenPhase_without_cut_critical

end JSP000404Research
