import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# Finite measurable packing on a finite-measure space

This file isolates the measure-theoretic core needed for the JSP-000404
support-arc argument.

If a finite family of measurable sets is pairwise disjoint, each set has
measure equal to a prescribed nonnegative real length, and the whole ambient
space has total measure T, then the sum of those lengths is at most T.

The theorem is completely geometry-free and will later be instantiated on the
angle circle of circumference 2*pi.
-/

namespace JSP000404Research

open scoped BigOperators MeasureTheory
open MeasureTheory Set

/-- Finite pairwise-disjoint measurable pieces cannot have total prescribed
real length exceeding the ambient finite measure. -/
theorem finite_disjoint_measurable_length_sum_le
    {X I : Type*}
    [MeasurableSpace X] [Fintype I]
    (mu : Measure X)
    (S : I → Set X)
    (len : I → ℝ)
    (T : ℝ)
    (hlen0 : ∀ i, 0 ≤ len i)
    (hmeas : ∀ i, MeasurableSet (S i))
    (hdisj : PairwiseDisjoint (Set.univ : Set I) S)
    (hmeasure : ∀ i, mu (S i) = ENNReal.ofReal (len i))
    (hambient : mu Set.univ = ENNReal.ofReal T)
    (hT0 : 0 ≤ T) :
    (∑ i, len i) ≤ T := by
  have hunion :
      mu (⋃ i : I, S i) = ∑ i : I, mu (S i) := by
    simpa using
      (measure_biUnion_finset
        (mu := mu)
        (s := (Finset.univ : Finset I))
        hdisj
        (fun i _ => hmeas i))
  have hsumMeasure :
      (∑ i : I, mu (S i)) ≤ mu Set.univ := by
    rw [← hunion]
    exact measure_mono (Set.subset_univ _)
  have hENN :
      (∑ i : I, ENNReal.ofReal (len i)) ≤
        ENNReal.ofReal T := by
    simpa [hmeasure, hambient] using hsumMeasure
  have hofRealSum :
      ENNReal.ofReal (∑ i : I, len i) =
        ∑ i : I, ENNReal.ofReal (len i) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i _
    exact hlen0 i
  rw [← hofRealSum] at hENN
  exact (ENNReal.ofReal_le_ofReal_iff hT0).1 hENN

#print axioms finite_disjoint_measurable_length_sum_le

end JSP000404Research
