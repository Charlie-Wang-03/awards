import JSP000404Research.LinearizedGap
import JSP000404Research.StrictExposure
import Mathlib.Tactic

/-!
# Exposure from a linearized ray cycle cut at a positive gap

Assume a cyclic family of projective rays has already been rotated so that the
chosen cut gap is the final gap.  Parameterize the remaining rays by prefix
sums of the other gaps.

If

* all gaps are nonnegative and sum to one projective half-circle,
* the final gap is positive,
* all rays on the complementary lift use one common sign,

then every projective parameter lies in an interval of width

  pi * (1 - finalGap) < pi.

The midpoint-direction argument therefore makes the centre strictly exposed.

A positive Sendov quotient on the final gap is enough to guarantee positive
gap width, because q_last <= t * gap_last and t>0.

This is the geometric bridge needed after the unique-transition gap has been
rotated to the end of the cyclic ray list.
-/

namespace JSP000404Research

open Real

/-- Every prefix avoids the last gap, so its mass is at most the total mass of
all non-last gaps. -/
theorem prefixGap_le_one_sub_last
    {m : ℕ} (hm : 0 < m)
    (gap : Fin m → ℝ)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (hgap : (∑ i, gap i) = 1)
    (j : Fin m) :
    prefixGap gap j ≤ 1 - gap (lastGapIndex m hm) := by
  classical
  let e := lastGapIndex m hm
  have hsubset :
      prefixIndices j ⊆ (Finset.univ : Finset (Fin m)).erase e := by
    intro r hr
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ r⟩
    intro hre
    subst r
    exact lastGap_not_mem_prefix hm j hr
  have hsum :
      prefixGap gap j ≤
        ∑ r ∈ (Finset.univ : Finset (Fin m)).erase e, gap r := by
    unfold prefixGap
    exact Finset.sum_le_sum_of_subset_of_nonneg
      hsubset
      (fun r _ _ => hgap0 r)
  have herase :
      (∑ r ∈ (Finset.univ : Finset (Fin m)).erase e, gap r)
        = 1 - gap e := by
    have hmem : e ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ e
    have hadd :=
      Finset.sum_erase_add _ gap hmem
    rw [hgap] at hadd
    linarith
  rw [herase] at hsum
  simpa [e] using hsum

/-- A positive quotient plus q <= t*gap and t>0 forces the gap itself to be
positive. -/
theorem gap_pos_of_positive_quotient
    {q : ℕ} {t gap : ℝ}
    (ht : 0 < t)
    (hq : q ≠ 0)
    (hfloor : (q : ℝ) ≤ t * gap) :
    0 < gap := by
  have hq1 : 1 ≤ q := by omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hprod : 0 < t * gap := by
    linarith
  rcases mul_pos_iff.mp hprod with hpos | hneg
  · exact hpos.2
  · exact False.elim ((not_lt_of_ge ht.le) hneg.1)

/-- Linearized common-sign rays obtained by cutting at a positive final gap
lie in a strict sub-pi interval and hence expose their centre. -/
theorem strictlyExposedAt_of_linearized_positive_last_gap
    {V : Type*} {p : V → Plane} {i : V}
    {m : ℕ} (hm : 0 < m)
    (gap : Fin m → ℝ)
    (hgap0 : ∀ r, 0 ≤ gap r)
    (hgap : (∑ r, gap r) = 1)
    (hlast : 0 < gap (lastGapIndex m hm))
    (a : ℝ)
    (sigma : Bool)
    (ray : Fin m → V)
    (rho : Fin m → ℝ)
    (hrho : ∀ r, 0 < rho r)
    (hsurj : ∀ j, j ≠ i → ∃ r, ray r = j)
    (hrepr : ∀ r,
      p (ray r) - p i =
        rho r •
          signedRayDirection sigma
            (a + Real.pi * prefixGap gap r)) :
    StrictlyExposedAt p i := by
  let width : ℝ :=
    Real.pi * (1 - gap (lastGapIndex m hm))
  have hlast_le_one :
      gap (lastGapIndex m hm) ≤ 1 := by
    have hnonneg_other :
        0 ≤ ∑ r ∈
          (Finset.univ : Finset (Fin m)).erase (lastGapIndex m hm),
          gap r :=
      Finset.sum_nonneg fun r _ => hgap0 r
    have hadd :=
      Finset.sum_erase_add
        (Finset.univ : Finset (Fin m))
        gap
        (Finset.mem_univ (lastGapIndex m hm))
    rw [hgap] at hadd
    linarith
  have hwidth0 : 0 ≤ width := by
    dsimp [width]
    exact mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hlast_le_one)
  have hwidthpi : width < Real.pi := by
    dsimp [width]
    have hunit :
        1 - gap (lastGapIndex m hm) < 1 := by
      linarith
    nlinarith [Real.pi_pos]
  apply strictlyExposedAt_of_common_signed_interval
    (p := p) (i := i) (a := a) (width := width)
    hwidth0 hwidthpi sigma
  intro j hji
  obtain ⟨r, hrj⟩ := hsurj j hji
  refine ⟨rho r,
    a + Real.pi * prefixGap gap r,
    hrho r, ?_, ?_, ?_⟩
  · have hp0 := prefixGap_nonneg gap hgap0 r
    nlinarith [Real.pi_pos]
  · have hple :=
      prefixGap_le_one_sub_last hm gap hgap0 hgap r
    dsimp [width]
    nlinarith [Real.pi_pos]
  · rw [← hrj]
    exact hrepr r

/-- Sendov quotient form: a positive final quotient automatically supplies
the positive cut gap required above. -/
theorem strictlyExposedAt_of_linearized_positive_last_quotient
    {V : Type*} {p : V → Plane} {i : V}
    {m : ℕ} (hm : 0 < m)
    (gap : Fin m → ℝ)
    (q : Fin m → ℕ)
    (t : ℝ)
    (ht : 0 < t)
    (hgap0 : ∀ r, 0 ≤ gap r)
    (hgap : (∑ r, gap r) = 1)
    (hfloor : ∀ r, (q r : ℝ) ≤ t * gap r)
    (hlastq : q (lastGapIndex m hm) ≠ 0)
    (a : ℝ)
    (sigma : Bool)
    (ray : Fin m → V)
    (rho : Fin m → ℝ)
    (hrho : ∀ r, 0 < rho r)
    (hsurj : ∀ j, j ≠ i → ∃ r, ray r = j)
    (hrepr : ∀ r,
      p (ray r) - p i =
        rho r •
          signedRayDirection sigma
            (a + Real.pi * prefixGap gap r)) :
    StrictlyExposedAt p i := by
  have hlast :
      0 < gap (lastGapIndex m hm) :=
    gap_pos_of_positive_quotient
      ht hlastq (hfloor (lastGapIndex m hm))
  exact strictlyExposedAt_of_linearized_positive_last_gap
    (p := p) (i := i) hm gap hgap0 hgap hlast
    a sigma ray rho hrho hsurj hrepr

#print axioms prefixGap_le_one_sub_last
#print axioms gap_pos_of_positive_quotient
#print axioms strictlyExposedAt_of_linearized_positive_last_gap
#print axioms strictlyExposedAt_of_linearized_positive_last_quotient

end JSP000404Research
