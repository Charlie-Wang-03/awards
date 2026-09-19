import JSP000404Research.GapRemainder
import JSP000404Research.UniqueGap
import Mathlib.Tactic

/-!
# Gap arcs avoiding the unique exceptional gap

At a unit-deficit centre there is a unique quotient-positive gap.  Any finite
subarc avoiding that gap consists entirely of quotient-zero gaps, hence its
total angular mass is bounded by `zeroGapMass`, and therefore by the
fractional remainder budget.

This file is purely finite/combinatorial.  The remaining geometric step is to
identify, for two rays in cyclic order, one of their two projective arcs with
such a finite subarc.
-/

namespace JSP000404Research

open scoped BigOperators

/-- A subset consisting only of zero-quotient gaps has mass at most the total
zero-gap mass. -/
theorem sum_gap_le_zeroGapMass_of_zero
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (s : Finset I)
    (hs : ∀ i ∈ s, q i = 0) :
    (∑ i ∈ s, gap i) ≤ zeroGapMass gap q := by
  classical
  unfold zeroGapMass
  calc
    (∑ i ∈ s, gap i)
        = ∑ i ∈ s, (if q i = 0 then gap i else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [hs i hi]
    _ ≤ ∑ i : I, (if q i = 0 then gap i else 0) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ s)
            (fun i _ _ => by
              by_cases hqi : q i = 0
              · simp [hqi, hgap0 i]
              · simp [hqi])

/-- Once the unique positive quotient index is fixed, every subset avoiding it
contains only zero-quotient gaps. -/
theorem all_zero_of_avoids_unique_positive
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    {e : I}
    (hepos : q e ≠ 0)
    (heunique : ∀ j, q j ≠ 0 → j = e)
    (s : Finset I)
    (hes : e ∉ s) :
    ∀ i ∈ s, q i = 0 := by
  intro i hi
  by_contra hqi
  have hie : i = e := heunique i hqi
  subst i
  exact hes hi

/-- Any subarc avoiding the unique exceptional gap is paid for by the total
zero-gap mass. -/
theorem sum_gap_le_zeroGapMass_of_avoids_unique
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (hgap0 : ∀ i, 0 ≤ gap i)
    {e : I}
    (hepos : q e ≠ 0)
    (heunique : ∀ j, q j ≠ 0 → j = e)
    (s : Finset I)
    (hes : e ∉ s) :
    (∑ i ∈ s, gap i) ≤ zeroGapMass gap q := by
  exact sum_gap_le_zeroGapMass_of_zero gap q hgap0 s
    (all_zero_of_avoids_unique_positive q hepos heunique s hes)

/-- Unit-deficit arc budget: every subarc avoiding the unique exceptional gap
has scaled mass at most `delta`. -/
theorem unit_deficit_arc_budget
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 2 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (hgap : (∑ i, gap i) = 1)
    (hQle : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 1)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    {e : I}
    (hepos : q e ≠ 0)
    (heunique : ∀ j, q j ≠ 0 → j = e)
    (s : Finset I)
    (hes : e ∉ s)
    (ht0 : 0 ≤ t) :
    t * (∑ i ∈ s, gap i) ≤ delta := by
  have hsub :=
    sum_gap_le_zeroGapMass_of_avoids_unique
      gap q hgap0 hepos heunique s hes
  have hbudget :=
    (unit_deficit_zero_gap_budget
      gap q n delta t hn ht hgap hQle hell hfloor).2.2
  exact (mul_le_mul_of_nonneg_left hsub ht0).trans hbudget

/-- Existence form using only the unit-deficit hypotheses. -/
theorem unit_deficit_exists_exceptional_arc_budget
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 2 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (hgap : (∑ i, gap i) = 1)
    (hQle : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 1)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    (ht0 : 0 ≤ t) :
    ∃ e : I, q e ≠ 0 ∧
      ∀ s : Finset I, e ∉ s →
        t * (∑ i ∈ s, gap i) ≤ delta := by
  obtain ⟨e, hepos, heunique⟩ :=
    unit_deficit_existsUnique_positive q n hn hQle hell
  refine ⟨e, hepos, ?_⟩
  intro s hes
  exact unit_deficit_arc_budget
    gap q n delta t hn ht hgap0 hgap hQle hell hfloor
    hepos heunique s hes ht0

#print axioms sum_gap_le_zeroGapMass_of_zero
#print axioms all_zero_of_avoids_unique_positive
#print axioms sum_gap_le_zeroGapMass_of_avoids_unique
#print axioms unit_deficit_arc_budget
#print axioms unit_deficit_exists_exceptional_arc_budget

end JSP000404Research
