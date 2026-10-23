import JSP000404Research.PositiveGapFifteenHardPhase
import Mathlib.Tactic

/-!
# Exact fifteen-sample threshold, without the coarse n >= 7 simplification

For the original uncompensated six-centre hard profile, the proof uses
  15 * delta < t = n + delta,
equivalently 14 * delta < n. The previously recorded n>=7 theorem is
a uniform corollary for 0<=delta<1/2; this module retains the sharp
parameter-dependent hypothesis and permits n=5 and n=6.

This only rules out a cover by canonical positive-quotient cyclic bad arcs.
No Boolean-hole payment, necessary domination of all hard blockers, or
resolution of JSP-000404 is claimed.
-/

namespace JSP000404Research

theorem six_point_hard_top_exists_safe_fifteenPhase_of_exact_threshold
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hthreshold : 14 * delta < (n : ℝ))
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    ∃ x : ℝ, 0 ≤ x ∧ x < t ∧
      ∀ u : GlobalPositiveGapSlot C t,
        ¬ GlobalCyclicPositiveGapBadAt C t delta u x := by
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hsep : delta < t / 15 := by
    rw [ht]
    linarith
  have hcard14 :
      Fintype.card (GlobalPositiveGapSlot C t) ≤ 14 :=
    six_point_no_compensation_positive_gap_card_le_fourteen
      hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
      top hTop hMin hNoTop
  by_contra hnone
  push Not at hnone
  have hnone' : ∀ r : Fin 15,
      ∃ u : GlobalPositiveGapSlot C t,
        GlobalCyclicPositiveGapBadAt C t delta u (fifteenPhase t r) := by
    intro r
    have hno := hnone (fifteenPhase t r)
      (fifteenPhase_nonneg htpos.le r)
      (fifteenPhase_lt_t htpos r)
    exact hno
  let slot : Fin 15 → GlobalPositiveGapSlot C t :=
    fun r => Classical.choose (hnone' r)
  have hbad :
      ∀ r : Fin 15,
        GlobalCyclicPositiveGapBadAt C t delta (slot r) (fifteenPhase t r) := by
    intro r
    exact Classical.choose_spec (hnone' r)
  have hinj : Function.Injective slot :=
    positive_gap_slot_assignment_on_fifteenPhase_injective
      C htpos hdelta0 hsep slot hbad
  have h15 : 15 ≤ Fintype.card (GlobalPositiveGapSlot C t) := by
    simpa using (Fintype.card_le_of_injective slot hinj)
  omega

theorem six_point_hard_top_exists_safe_fifteenPhase_n_six
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (3 : ℝ) / 7)
    (ht : t = (6 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = 5)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t 6) :
    ∃ x : ℝ, 0 ≤ x ∧ x < t ∧
      ∀ u : GlobalPositiveGapSlot C t,
        ¬ GlobalCyclicPositiveGapBadAt C t delta u x := by
  exact six_point_hard_top_exists_safe_fifteenPhase_of_exact_threshold
    hp hcap C hcard (by omega : 5 ≤ 6) hdelta0
    (by linarith : delta < (1 : ℝ) / 2)
    ht hlam (by linarith : 14 * delta < (6 : ℝ))
    top hTop hMin hNoTop

#print axioms six_point_hard_top_exists_safe_fifteenPhase_of_exact_threshold
#print axioms six_point_hard_top_exists_safe_fifteenPhase_n_six

end JSP000404Research
