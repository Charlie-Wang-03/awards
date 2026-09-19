import JSP000404Research.PhaseArithmetic
import JSP000404Research.PhaseObstruction
import Mathlib.Tactic

/-!
# Arithmetic closure from a global critical-turn budget

The current lower-branch geometric target is a finite family of critical
adjacent sign-transition gaps with normalized widths s c satisfying

  1 <= s c

and the global total-turn estimate

  sum_c s c <= 2 * (n + delta).

Because the family cardinality is integral and delta < 1/2, these two facts
already imply

  card C <= 2*n.

Combined with the existing short-obstruction bound (each bad phase interval
has length at most delta), this is exactly the count needed by the phase-cover
contradiction.

This module intentionally contains no geometry: proving the total-turn estimate
is the remaining global geometric obligation.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Unit lower bounds on critical widths turn total width into a cardinality
bound. -/
theorem critical_card_real_le_sum
    {C : Type*} [Fintype C]
    (s : C → ℝ)
    (hone : ∀ c, 1 ≤ s c) :
    (Fintype.card C : ℝ) ≤ ∑ c, s c := by
  have hsum :
      (∑ _c : C, (1 : ℝ)) ≤ ∑ c : C, s c :=
    Finset.sum_le_sum fun c _ => hone c
  simpa using hsum

/-- Global total critical width at most 2(n+delta) implies at most 2n critical
transitions in the lower branch. -/
theorem critical_card_le_two_n_of_total_turn
    {C : Type*} [Fintype C]
    (s : C → ℝ)
    {n : ℕ} {delta : ℝ}
    (hdelta : delta < (1 : ℝ) / 2)
    (hone : ∀ c, 1 ≤ s c)
    (htotal : (∑ c, s c) ≤ 2 * ((n : ℝ) + delta)) :
    Fintype.card C ≤ 2 * n := by
  apply hull_count_upper hdelta
  exact (critical_card_real_le_sum s hone).trans htotal

/-- Phase-cover contradiction in the exact form needed after the geometric
total-turn lemma is supplied. -/
theorem critical_intervals_cannot_cover_of_total_turn
    {C : Type*} [Fintype C]
    (s : C → ℝ)
    {n : ℕ} {delta : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hone : ∀ c, 1 ≤ s c)
    (htotal : (∑ c, s c) ≤ 2 * ((n : ℝ) + delta)) :
    ¬ ((n : ℝ) + delta ≤ (Fintype.card C : ℝ) * delta) := by
  intro hcover
  have hlow :=
    phase_cover_count_lower
      (n := n) (m := Fintype.card C)
      hn hdelta0 hdelta hcover
  have hhigh :=
    critical_card_le_two_n_of_total_turn
      s hdelta hone htotal
  omega

/-- Abstract good-phase outlet: if all phases being bad would force the
critical family to cover the phase circle, the global turn budget produces a
good phase. -/
theorem exists_good_phase_of_critical_total_turn
    {Phase C : Type*} [Nonempty Phase] [Fintype C]
    (Bad : Phase → Prop)
    (s : C → ℝ)
    {n : ℕ} {delta : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hone : ∀ c, 1 ≤ s c)
    (htotal : (∑ c, s c) ≤ 2 * ((n : ℝ) + delta))
    (hallbad_cover :
      (∀ phase, Bad phase) →
        (n : ℝ) + delta ≤ (Fintype.card C : ℝ) * delta) :
    ∃ phase, ¬ Bad phase := by
  have hcount :=
    critical_card_le_two_n_of_total_turn s hdelta hone htotal
  exact exists_good_phase_of_bad_cover_count
    Bad hn hdelta0 hdelta hcount hallbad_cover

#print axioms critical_card_real_le_sum
#print axioms critical_card_le_two_n_of_total_turn
#print axioms critical_intervals_cannot_cover_of_total_turn
#print axioms exists_good_phase_of_critical_total_turn

end JSP000404Research
