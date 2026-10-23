import JSP000404Research.OrdinaryCriticalHalfGrid
import JSP000404Research.FinitePeriodTransitionPhaseCover
import Mathlib.Tactic

/-!
# No actual ordinary-critical unit-gap cover of the finite phase period (n>=5)

This theorem removes the CONDITIONAL quantitative phase-cover lower bound
from the earlier finite-period exclusion theorem, for the ACTUAL ordinary
critical unit-gap interval predicate and strictly positive delta.

We prove it instead via a genuine finite half-grid pigeonhole argument:
2*n+1 distinct half-grid phases, at most ten unit-gap slots, and a single
critical interval width <= delta < 1/2, so each slot can contain at most
one half-grid phase. For n>=5 there is an uncovered half-grid phase.

The endpoint r=2*n is strictly within [0,t) when delta>0, since
t=n+delta. This explains the explicit delta>0 hypothesis. The degenerate
delta=0 case is not claimed by this theorem.

This excludes a very specific *ordinary critical transition-only* phase
cover. It does NOT establish that all dyadic Boolean-hole/payment blockers
must be of this kind: original wrap, mixed and rigid debts remain open.
-/

namespace JSP000404Research

theorem no_six_point_ordinary_critical_finite_period_cover_of_delta_pos
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hn5 : 5 ≤ n)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (S : Finset (GlobalUnitGapSlot C t)) :
    ¬ FinitePeriodCovers t
      (OrdinaryCriticalUnitBadAt C t delta) S := by
  obtain ⟨r, hr⟩ :=
    exists_uncovered_halfGrid_phase_of_six_point_terminal
      C hn4 hn5 hdeltaPos.le hdeltaHalf ht
      hcard top hTop hMin
  have hrbound : r.val ≤ 2*n := by omega
  have hrboundR : (r.val : ℝ) ≤ 2*(n : ℝ) := by
    exact_mod_cast hrbound
  have hxle : (r.val : ℝ) / 2 ≤ (n : ℝ) := by
    linarith
  have hnt : (n : ℝ) < t := by rw [ht]; linarith
  have hxlt : (r.val : ℝ) / 2 < t :=
    lt_of_le_of_lt hxle hnt
  intro hcover
  obtain ⟨u, _huS, hubad⟩ :=
    hcover ((r.val : ℝ) / 2)
      (by positivity) hxlt
  exact hr u hubad

#print axioms no_six_point_ordinary_critical_finite_period_cover_of_delta_pos

end JSP000404Research
