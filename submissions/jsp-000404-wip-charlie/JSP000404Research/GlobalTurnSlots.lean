import JSP000404Research.PhaseObstruction
import Mathlib.Tactic

/-!
# Global convex-hull turn-slot closure

A pointwise allocation of obstruction slots to individual hull normal cones is
stronger than necessary.  The robust object is the entire unwrapped turning
path of the convex hull.

Its normalized total length is

  2 * (n + delta).

If the geometry injects the m bad-phase components into disjoint unit slots
along that global turning path, it yields only the real inequality

  m <= 2 * (n + delta).

Because m is integral and delta < 1/2, PhaseArithmetic rounds this to m <= 2n.
Combined with the delta-cover lower bound, this already forces a good phase.

This is the preferred arithmetic shell for the current JSP-000404 lower-branch
search; it does not require taking floors separately at each hull vertex.
-/

namespace JSP000404Research

/-- A global turn-length bound on the obstruction count already closes the
phase contradiction. -/
theorem exists_good_phase_of_global_turn_slots
    {Phase : Type*} [Nonempty Phase]
    (Bad : Phase → Prop)
    {n m : ℕ} {delta : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hslots : (m : ℝ) ≤ 2 * ((n : ℝ) + delta))
    (hallbad_cover :
      (∀ phase, Bad phase) →
        (n : ℝ) + delta ≤ (m : ℝ) * delta) :
    ∃ phase, ¬ Bad phase := by
  have hm : m ≤ 2 * n :=
    hull_count_upper hdelta hslots
  exact exists_good_phase_of_bad_cover_count
    Bad hn hdelta0 hdelta hm hallbad_cover

/-- Contradiction form under an all-bad assumption. -/
theorem global_turn_slots_cannot_cover
    {n m : ℕ} {delta : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hslots : (m : ℝ) ≤ 2 * ((n : ℝ) + delta)) :
    ¬ ((n : ℝ) + delta ≤ (m : ℝ) * delta) := by
  intro hcover
  have hm : m ≤ 2 * n := hull_count_upper hdelta hslots
  have hlower := phase_cover_count_lower
    hn hdelta0 hdelta hcover
  omega

#print axioms exists_good_phase_of_global_turn_slots
#print axioms global_turn_slots_cannot_cover

end JSP000404Research
