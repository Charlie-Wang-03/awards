import JSP000404Research.PlanarThreeSevenThreeZeroGapBudget
import Mathlib.Tactic

/-!
# Quantitative real-gap obstruction for seven n=3 planar centres

An original n=3 lower-strip AngleCap set with >=7 centres has one
actual centre with >=3 distinct strictly positive zero-quotient gaps.
Their total scaled width is <= delta. Thus at least ONE of these
three true gaps has width <= delta/(3*t).

We prove an integral-free finite averaging lemma first, then use
the existing kernel-certified original planar three-zero-gap ledger.
No global debt payment or synthetic Boolean holes are assumed.
-/

namespace JSP000404Research
open scoped BigOperators

/-- Finite pigeonhole for a nonnegative weighted finite family:
if three or more entries have sum <= d, one actual member has
three times its value <= d. -/
theorem exists_three_way_small_summand
    {I : Type*} [DecidableEq I] (S : Finset I)
    (f : I → ℝ) (d : ℝ)
    (hcard : 3 ≤ S.card)
    (hsum : (∑ i ∈ S, f i) ≤ d) :
    ∃ i ∈ S, 3 * f i ≤ d := by
  classical
  by_contra hnone
  push Not at hnone
  have hstrict : ∀ i ∈ S, d < 3 * f i := by
    intro i hi
    exact lt_of_not_ge (hnone i hi)
  have hsumstrict : (∑ i ∈ S, d) < (∑ i ∈ S, 3 * f i) := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (hstrict i hi).le
    · obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      exact ⟨i,hi,hstrict i hi⟩
  have hcount : (∑ _i ∈ S, d) = (S.card : ℝ) * d := by simp
  have hscale : (∑ i ∈ S, 3 * f i) = 3 * (∑ i ∈ S, f i) := by
    rw [Finset.mul_sum]
  have hd0 : 0 ≤ d := by
    by_contra hd
    have hh : (S.card : ℝ) ≥ 3 := by exact_mod_cast hcard
    have hq : (S.card : ℝ) * d ≤ 3 * d := by
      exact mul_le_mul_of_nonpos_right hh hd.le
    rw [hcount, hscale] at hsumstrict
    linarith
  have hcardR : (3 : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hcard
  rw [hcount, hscale] at hsumstrict
  have hm : 3 * d ≤ (S.card : ℝ) * d :=
    mul_le_mul_of_nonneg_right hcardR hd0
  linarith

/-- In ORIGINAL seven-or-more-point n=3 AngleCap geometry, a real
projective gap of zero integer quotient must be <= delta/(3*t),
where the factor 3 is paid by THREE DISTINCT gaps at the same
original centre, not by three credits reused across owners. -/
theorem planar_three_seven_has_zero_gap_one_third_slack
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 7 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ∃ i : V, ∃ r : Fin (C i).gaps.length,
      centreQuotient (C i) t r = 0 ∧
      0 < (C i).gaps.get r ∧
      3 * (t * (C i).gaps.get r) ≤ delta := by
  classical
  obtain ⟨i,hzeros,hpos,hslack⟩ :=
    planar_three_seven_forces_three_positive_zero_gaps_with_total_slack
      hp hcap hcard hdelta0 hdeltaHalf ht hlam C
  let S : Finset (Fin (C i).gaps.length) :=
    Finset.univ.filter (fun r => centreQuotient (C i) t r = 0)
  have hsmall :=
    exists_three_way_small_summand S
      (fun r => t * (C i).gaps.get r) delta hzeros hslack
  obtain ⟨r,hr,hbound⟩ := hsmall
  have hq : centreQuotient (C i) t r = 0 :=
    (Finset.mem_filter.mp hr).2
  exact ⟨i,r,hq,hpos r hq,hbound⟩

#print axioms exists_three_way_small_summand
#print axioms planar_three_seven_has_zero_gap_one_third_slack

end JSP000404Research
