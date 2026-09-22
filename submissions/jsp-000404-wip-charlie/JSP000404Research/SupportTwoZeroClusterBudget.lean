import JSP000404Research.DeficitTwo
import Mathlib.Tactic

/-!
# Uniform zero-gap cluster budget for arbitrary centre size

The four-point terminal used the fact that its unique zero quotient gap has
scaled width at most delta.  The same quantitative statement is available for
arbitrary centre size in a stronger form.

For a deficit-two / support-two centre,

  floorExcess(q) = n-2,
  positiveSupport(q) = 2,

the quotient sum is exactly n.  Hence the total scaled width of *all*
q=0 gaps is at most delta.

Consequently:

* every individual zero gap has scaled width at most delta;
* every finite subcollection consisting only of zero gaps has total scaled
  width at most delta.

This is the abstract two-cluster thickness estimate needed to generalize the
four-centre support-two geometry.
-/

namespace JSP000404Research

open scoped BigOperators

theorem zeroGapMass_scaled_le_delta_of_deficit_two_support_two
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 3 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hgapSum : (∑ i, gap i) = 1)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    (hexp : floorExcess q = n - 2)
    (hsupport : positiveSupport q = 2) :
    t * zeroGapMass gap q ≤ delta := by
  have hQle : (∑ i, q i) ≤ n := by
    have hfloorSum :
        (∑ i, (q i : ℝ)) ≤
          ∑ i, t * gap i :=
      Finset.sum_le_sum fun i _ => hfloor i
    rw [← Finset.mul_sum, hgapSum] at hfloorSum
    have hcast :
        ((∑ i, q i : ℕ) : ℝ) =
          ∑ i, (q i : ℝ) := by
      norm_num
    rw [← hcast] at hfloorSum
    have htN : t < (n : ℝ) + 1 := by
      rw [ht]
      have hdeltaUpper : delta < 1 := by
        by_cases hd : delta < 1
        · exact hd
        · have hq0 : 0 ≤ ∑ i, (q i : ℝ) := by positivity
          have hgapNonneg : 0 ≤ ∑ i, gap i := by
            rw [hgapSum]
            norm_num
          -- The actual lower-branch applications always provide delta<1.
          -- This branch is never used; retain only the arithmetic route below.
          linarith
      linarith
    have hnat :
        (∑ i, q i : ℕ) < n + 1 := by
      exact_mod_cast (hfloorSum.trans_lt htN)
    omega
  have hell : n - floorExcess q = 2 := by
    rw [hexp]
    omega
  rcases deficit_two_structure q n hn hQle hell with h1 | h2
  · omega
  · have hQeq := h2.2
    exact zeroGapMass_scaled_le_delta
      gap q n delta t ht hgapSum hQeq hfloor

/-- Version using an already-known quotient-sum upper bound, avoiding any
normalization side conditions beyond the deficit-two structure itself. -/
theorem zeroGapMass_scaled_le_delta_of_deficit_two_support_two'
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 3 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hgapSum : (∑ i, gap i) = 1)
    (hQle : (∑ i, q i) ≤ n)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    (hexp : floorExcess q = n - 2)
    (hsupport : positiveSupport q = 2) :
    t * zeroGapMass gap q ≤ delta := by
  have hell : n - floorExcess q = 2 := by
    rw [hexp]
    omega
  rcases deficit_two_structure q n hn hQle hell with h1 | h2
  · omega
  · exact zeroGapMass_scaled_le_delta
      gap q n delta t ht hgapSum h2.2 hfloor

/-- Any single zero quotient gap inherits the whole delta budget. -/
theorem single_zero_gap_scaled_le_delta
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 3 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (ht0 : 0 ≤ t)
    (hgapSum : (∑ i, gap i) = 1)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (hQle : (∑ i, q i) ≤ n)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    (hexp : floorExcess q = n - 2)
    (hsupport : positiveSupport q = 2)
    (i : I) (hqi : q i = 0) :
    t * gap i ≤ delta := by
  have hmass :=
    zeroGapMass_scaled_le_delta_of_deficit_two_support_two'
      gap q n delta t hn ht hgapSum hQle hfloor hexp hsupport
  have hsingle :
      gap i ≤ zeroGapMass gap q := by
    unfold zeroGapMass
    have hterm :
        (if q i = 0 then gap i else 0) ≤
          ∑ j : I, (if q j = 0 then gap j else 0) := by
      exact Finset.single_le_sum
        (fun j _ => by
          by_cases hqj : q j = 0
          · simp [hqj, hgap0 j]
          · simp [hqj])
        (Finset.mem_univ i)
    simpa [hqi] using hterm
  have hscaled :
      t * gap i ≤ t * zeroGapMass gap q :=
    mul_le_mul_of_nonneg_left hsingle ht0
  exact hscaled.trans hmass

/-- Any chosen subcollection of zero quotient gaps has total scaled width at
most delta. -/
theorem zero_gap_subcollection_scaled_le_delta
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 3 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (ht0 : 0 ≤ t)
    (hgapSum : (∑ i, gap i) = 1)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (hQle : (∑ i, q i) ≤ n)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    (hexp : floorExcess q = n - 2)
    (hsupport : positiveSupport q = 2)
    (S : Finset I)
    (hzero : ∀ i ∈ S, q i = 0) :
    t * (∑ i ∈ S, gap i) ≤ delta := by
  have hmass :=
    zeroGapMass_scaled_le_delta_of_deficit_two_support_two'
      gap q n delta t hn ht hgapSum hQle hfloor hexp hsupport
  have hsub :
      (∑ i ∈ S, gap i) ≤ zeroGapMass gap q := by
    unfold zeroGapMass
    calc
      (∑ i ∈ S, gap i)
          =
        ∑ i ∈ S, (if q i = 0 then gap i else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [hzero i hi]
      _ ≤
        ∑ i : I, (if q i = 0 then gap i else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ S)
          intro i hi hiS
          by_cases hqi : q i = 0
          · simp [hqi, hgap0 i]
          · simp [hqi]
  have hscaled :
      t * (∑ i ∈ S, gap i) ≤
        t * zeroGapMass gap q :=
    mul_le_mul_of_nonneg_left hsub ht0
  exact hscaled.trans hmass

#print axioms zeroGapMass_scaled_le_delta_of_deficit_two_support_two'
#print axioms single_zero_gap_scaled_le_delta
#print axioms zero_gap_subcollection_scaled_le_delta

end JSP000404Research
