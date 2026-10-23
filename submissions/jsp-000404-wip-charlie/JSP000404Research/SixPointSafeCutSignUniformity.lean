import JSP000404Research.CutTransitionSeedCriticalSlot
import JSP000404Research.BoundaryCutShift
import JSP000404Research.CyclicCriticalUnitPhase
import Mathlib.Tactic

/-!
# A genuine common cut with uniform sign on every short centre boundary arc

In the six-centre top-(n-1) / five-(n-3) profile (n>=5), eleven periodic
half-sample points give a phase x outside the actual cyclic q=1 critical
bad arcs of ALL centres. Shift the physical cut x*pi/t backwards by
delta*pi/t. At the resulting projective cut c, every opposite-sign pair of
rays within the short normalized boundary band [0,1+delta] would generate
an adjacent critical slot at x (or at x+t), contradicting the sample choice.

This strengthens bare noncoverage to a single original-geometry cut
that works for all centres at once. The short boundary arc may be empty,
and this statement does NOT pay global TRUE Boolean holes, projected-loss,
NET duplicates, soft/twin/mixed-rigid dyadic deficits, or wrap-hard sources.
-/

namespace JSP000404Research

/-- There is one actual projective cut whose short boundary band has a
constant cut-adjusted ray sign at EVERY original centre. -/
theorem six_point_exists_common_cut_short_band_sign_uniform
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hn4 : 4 ≤ n)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3) :
    ∃ c : ℝ, 0 ≤ c ∧ c < Real.pi ∧
      ∀ i : V, ∀ j k : OtherVertex i,
        cutNormalizedRayTheta hp t c i j ≤ 1 + delta →
        cutNormalizedRayTheta hp t c i k ≤ 1 + delta →
        cutRaySign hp c i j = cutRaySign hp c i k := by
  obtain ⟨r, hr⟩ :=
    exists_uncovered_elevenPhase_of_six_point_terminal
      C hn4 hn5 hdelta0 hdeltaHalf ht hcard top hTop hMin
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  let x : ℝ := elevenPhase t r
  have hx0 : 0 ≤ x := elevenPhase_nonneg htpos.le r
  have hxt : x < t := elevenPhase_lt_t htpos r
  let c₀ : ℝ := x * Real.pi / t
  have hc₀0 : 0 ≤ c₀ := by
    dsimp [c₀]
    positivity
  have hc₀pi : c₀ < Real.pi := by
    dsimp [c₀]
    apply (div_lt_iff₀ htpos).2
    nlinarith [mul_lt_mul_of_pos_right hxt Real.pi_pos]
  have hc₀phase : t * c₀ / Real.pi = x := by
    dsimp [c₀]
    field_simp [Real.pi_ne_zero, ne_of_gt htpos] <;> ring
  let c : ℝ := boundaryShortCut t delta c₀
  have hc0 : 0 ≤ c :=
    boundaryShortCut_nonneg (by omega : 1 ≤ n)
      ht hdelta0 hc₀0 hc₀pi
  have hcpi : c < Real.pi :=
    boundaryShortCut_lt_pi (by omega : 1 ≤ n)
      ht hdelta0 hc₀0 hc₀pi
  have hphase :
      t * c / Real.pi + delta = x ∨
        t * c / Real.pi + delta = x + t := by
    have h :=
      boundaryShort_phase_eq_or_add_period
        (by omega : 1 ≤ n) htpos ht hdelta0 hc₀0 hc₀pi
    dsimp [c] at h ⊢
    simpa only [hc₀phase] using h
  refine ⟨c, hc0, hcpi, ?_⟩
  intro i j k hjShort hkShort
  by_contra hsign
  have hjArc :
      0 ≤ cutNormalizedRayTheta hp t c i j ∧
        cutNormalizedRayTheta hp t c i j ≤ 1 + delta :=
    ⟨cutNormalizedRayTheta_nonneg hp htpos.le hc0 hcpi i j, hjShort⟩
  have hkArc :
      0 ≤ cutNormalizedRayTheta hp t c i k ∧
        cutNormalizedRayTheta hp t c i k ≤ 1 + delta :=
    ⟨cutNormalizedRayTheta_nonneg hp htpos.le hc0 hcpi i k, hkShort⟩
  have hjk : j ≠ k := by
    intro heq
    exact hsign (congrArg (cutRaySign hp c i) heq)
  obtain ⟨u, _, hbad⟩ :=
    cut_transition_seed_has_cyclic_critical_slot
      hp hcap C htpos hlam hdeltaHalf hc0 hcpi
      i hjk hsign hjArc hkArc
  rcases hphase with heq | heq
  · have hbadx : GlobalCyclicCriticalUnitBadAt C t delta u x := by
      simpa only [heq] using hbad
    exact hr u hbadx
  · have hbadxt : GlobalCyclicCriticalUnitBadAt C t delta u (x + t) := by
      simpa only [heq] using hbad
    have hbadx :=
      globalCyclicCriticalUnitBadAt_sub_period C u x hbadxt
    exact hr u hbadx

#print axioms six_point_exists_common_cut_short_band_sign_uniform

end JSP000404Research
