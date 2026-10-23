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

/-- All allowed lower-branch remainders, INCLUDING the degenerate delta=0
case, exclude a finite-period cover by actual ordinary critical unit slots.

For delta=0 the bad intervals have zero width. Eleven distinct quarter-grid
phases in [0,t) cannot be captured by ten available unit-gap slots. For
delta>0 the preceding half-grid argument gives the stronger result.

Unlike older conditional phase-cover terminals, this theorem requires NO
measure bound or irredundant-cover hypothesis. -/
theorem no_six_point_ordinary_critical_finite_period_cover
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
      centreExponent (C i) t = n - 3)
    (S : Finset (GlobalUnitGapSlot C t)) :
    ¬ FinitePeriodCovers t
      (OrdinaryCriticalUnitBadAt C t delta) S := by
  rcases lt_or_eq_of_le hdelta0 with hpos | hzero
  · exact
      no_six_point_ordinary_critical_finite_period_cover_of_delta_pos
        C hn4 hn5 hpos hdeltaHalf ht hcard top hTop hMin S
  · classical
    intro hcover
    have hcovered :
        ∀ r : Fin 11,
          ∃ u : GlobalUnitGapSlot C t,
            u ∈ S ∧
            OrdinaryCriticalUnitBadAt C t delta
              u ((r.val : ℝ) / 4) := by
      intro r
      have hr10 : r.val ≤ 10 := by have := r.isLt; omega
      have hrR : (r.val : ℝ) ≤ 10 := by exact_mod_cast hr10
      have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn5
      have hxlt : (r.val : ℝ) / 4 < t := by
        rw [ht]
        linarith
      exact hcover ((r.val : ℝ) / 4) (by positivity) hxlt
    let slot : Fin 11 → GlobalUnitGapSlot C t :=
      fun r => Classical.choose (hcovered r)
    have hbad :
        ∀ r : Fin 11,
          OrdinaryCriticalUnitBadAt C t delta
            (slot r) ((r.val : ℝ) / 4) := by
      intro r
      exact (Classical.choose_spec (hcovered r)).2
    have hinj : Function.Injective slot := by
      intro a b hab
      have hba :
          OrdinaryCriticalUnitBadAt C t delta
            (slot a) ((b.val : ℝ) / 4) := by
        rw [hab]
        exact hbad b
      have hdist :=
        ordinaryCriticalUnitBadAt_pair_distance_le_delta
          C t delta (slot a) (hbad a) hba
      rw [hzero] at hdist
      have hdiff :
          ((a.val : ℝ) / 4) - ((b.val : ℝ) / 4) = 0 := by
        have habs : |((a.val : ℝ) / 4) - ((b.val : ℝ) / 4)| = 0 :=
          le_antisymm hdist (abs_nonneg _)
        exact sub_eq_zero.mpr (abs_eq_zero.mp habs)
      have heqR : (a.val : ℝ) = (b.val : ℝ) := by linarith
      have heqN : a.val = b.val := by exact_mod_cast heqR
      exact Fin.ext heqN
    have hmore : 11 ≤ Fintype.card (GlobalUnitGapSlot C t) := by
      simpa using Fintype.card_le_of_injective slot hinj
    have hten : Fintype.card (GlobalUnitGapSlot C t) ≤ 10 :=
      six_point_globalUnitGapSlot_card_le_ten C hn4
        hdelta0 (by linarith : delta < 1) ht
        hcard top hTop hMin
    omega

#print axioms no_six_point_ordinary_critical_finite_period_cover

#print axioms no_six_point_ordinary_critical_finite_period_cover_of_delta_pos

end JSP000404Research
