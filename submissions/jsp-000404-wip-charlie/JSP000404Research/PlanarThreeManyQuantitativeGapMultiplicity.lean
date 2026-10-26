import JSP000404Research.PlanarHighSupportMultiplicity
import JSP000404Research.PlanarThreeSevenThreeZeroGapBudget
import JSP000404Research.ThreeFiveSaturatedUnitQuotients
import JSP000404Research.AngleCapStrictProjectiveTheta
import Mathlib.Tactic

/-!
# Original n=3 large configurations force many genuinely narrow gaps

At n=3, EVERY original high-support centre has exactly three unit
quotients and no local dyadic exponent. If there are N>=7 original
centres, the N-1 projective gaps contain EXACTLY N-4 zero quotients,
all strictly positive and sharing only ONE global per-centre delta
remainder. Thus one actual zero gap at every high-support centre
has scaled width at most delta/(N-4).

At least N-6 original centres are high-support by independently
kernel-verified strict-support arc packing. Both estimates use the
original AngleCap plane geometry: no synthetic Boolean holes or
re-used global payment credits are asserted.
-/

namespace JSP000404Research
open scoped BigOperators

/-- For a finite set of at least k>=1 real summands, sum <= d and
d>=0 imply one actual summand x obeys k*x <= d. Positivity of
each summand is not required for this elementary averaging lemma. -/
theorem exists_k_way_small_summand
    {I : Type*} [DecidableEq I]
    (S : Finset I) (f : I → ℝ) (d : ℝ) (k : ℕ)
    (hk : 1 ≤ k)
    (hcard : k ≤ S.card)
    (hd0 : 0 ≤ d)
    (hsum : (∑ i ∈ S, f i) ≤ d) :
    ∃ i ∈ S, (k : ℝ) * f i ≤ d := by
  classical
  by_contra hnone
  push Not at hnone
  have hstrict : ∀ i ∈ S, d < (k : ℝ) * f i := by
    intro i hi
    exact hnone i hi
  have hsumstrict :
      (∑ i ∈ S, d) < (∑ i ∈ S, (k : ℝ) * f i) := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (hstrict i hi).le
    · obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      exact ⟨i, hi, hstrict i hi⟩
  have hcount : (∑ _i ∈ S, d) = (S.card : ℝ) * d := by simp
  have hscale :
      (∑ i ∈ S, (k : ℝ) * f i) =
        (k : ℝ) * (∑ i ∈ S, f i) := by
    rw [Finset.mul_sum]
  have hcardR : (k : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hcard
  rw [hcount, hscale] at hsumstrict
  have hm : (k : ℝ) * d ≤ (S.card : ℝ) * d :=
    mul_le_mul_of_nonneg_right hcardR hd0
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  nlinarith

/-- For EVERY high-support original centre in a genuine n=3
configuration of N>=7 centres, one of its original strictly
positive zero-floor gaps has (N-4)*t*gap <= delta.

This improves the earlier single-centre three-gap statement in
two ways: it holds at EACH high-support centre, and the factor
N-4 grows with the actual number of original centres. -/
theorem planar_three_every_high_support_centre_has_narrow_gap
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
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (i : V)
    (hsupport : 3 ≤ positiveSupport (centreQuotient (C i) t)) :
    ∃ r : Fin (C i).gaps.length,
      centreQuotient (C i) t r = 0 ∧
      0 < (C i).gaps.get r ∧
      ((Fintype.card V - 4 : ℕ) : ℝ) *
        (t * (C i).gaps.get r) ≤ delta := by
  classical
  obtain ⟨_hk, hsup, hmass⟩ :=
    three_scale_high_support_exact_rigidity
      (C i) hdelta0 hdeltaHalf ht hsupport
  have hother :
      Fintype.card (OtherVertex i) = Fintype.card V - 1 := by
    change Fintype.card {j : V // j ≠ i} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl (fun j : V => j = i),
      Fintype.card_subtype_eq]
  have hraylen : (C i).rays.length = Fintype.card (OtherVertex i) := by
    rw [← List.toFinset_card_of_nodup (C i).nodup, (C i).complete]
    simp
  have hgaplen : (C i).gaps.length = Fintype.card V - 1 := by
    rw [(C i).gaps_length, hraylen, hother]
  let S : Finset (Fin (C i).gaps.length) :=
    Finset.univ.filter (fun r => centreQuotient (C i) t r = 0)
  have hzeros :
      S.card = Fintype.card V - 4 := by
    have hh :=
      quotient_zero_filter_card_eq_total_sub_support
        (centreQuotient (C i) t)
    have hbase : S.card = (C i).gaps.length - 3 := by
      simpa [S, hsup] using hh
    omega
  have htotal :
      (∑ r ∈ S, t * (C i).gaps.get r) ≤ delta := by
    simpa [S] using
      (saturated_centre_zero_gap_total_le_slack
        (C i) 3 hdelta0 ht hmass)
  obtain ⟨r, hr, hsmall⟩ :=
    exists_k_way_small_summand S
      (fun r => t * (C i).gaps.get r) delta
      (Fintype.card V - 4)
      (by omega) (by omega) hdelta0 htotal
  have hq : centreQuotient (C i) t r = 0 :=
    (Finset.mem_filter.mp hr).2
  have htpos : 0 < t := by rw [ht]; linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hgapPos : 0 < (C i).gaps.get r :=
    centreProjectiveCycle_gaps_pos_of_AngleCap
      hp hcap hlampos i (C i) _ (List.get_mem _ _)
  exact ⟨r, hq, hgapPos, hsmall⟩

/-- At least N-6 original centres in n=3 geometry each admit a
DISTINCT-CENTRE witness to the (N-4)-factor narrow-gap condition.
There is no assertion that the witness gap indices are disjoint
across different centres or that they are Boolean exterior holes. -/
theorem planar_three_many_centres_narrow_gap_witness_count
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
    ((Finset.univ : Finset V).filter
      (fun i => ∃ r : Fin (C i).gaps.length,
        centreQuotient (C i) t r = 0 ∧
        0 < (C i).gaps.get r ∧
        ((Fintype.card V - 4 : ℕ) : ℝ) *
          (t * (C i).gaps.get r) ≤ delta)).card
      + 6 ≥ Fintype.card V := by
  classical
  let H : Finset V :=
    Finset.univ.filter
      (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))
  let P : Finset V :=
    Finset.univ.filter
      (fun i => ∃ r : Fin (C i).gaps.length,
        centreQuotient (C i) t r = 0 ∧
        0 < (C i).gaps.get r ∧
        ((Fintype.card V - 4 : ℕ) : ℝ) *
          (t * (C i).gaps.get r) ≤ delta)
  have hsub : H ⊆ P := by
    intro i hi
    have hh : 3 ≤ positiveSupport (centreQuotient (C i) t) :=
      (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, planar_three_every_high_support_centre_has_narrow_gap
        hp hcap hcard hdelta0 hdeltaHalf ht hlam C i hh⟩
  have hc : H.card + 6 ≥ Fintype.card V := by
    simpa [H] using
      (planar_three_high_support_card_add_six_ge_total
        hp hcap hdelta0 hdeltaHalf ht hlam C)
  have hle := Finset.card_le_card hsub
  change P.card + 6 ≥ Fintype.card V
  omega

#print axioms exists_k_way_small_summand
#print axioms planar_three_every_high_support_centre_has_narrow_gap
#print axioms planar_three_many_centres_narrow_gap_witness_count

end JSP000404Research
