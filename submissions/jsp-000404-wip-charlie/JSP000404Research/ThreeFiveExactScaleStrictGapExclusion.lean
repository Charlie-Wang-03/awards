import JSP000404Research.AngleCapStrictProjectiveTheta
import JSP000404Research.ThreeScaleZeroGapSlack
import Mathlib.Tactic

/-!
# New ORIGINAL planar strict-gap exclusion at exactly t=3, five centres

The original AngleCap forces all canonical projective gaps at any
actual centre to be STRICTLY positive. With five original vertices,
every centre has exactly FOUR projective gaps. If the sum of their
natural floor quotients at t=3 were 3, at least one of these four
floor quotients would vanish.

The previously certified nonnegative-remainder ledger then bounds the
scaled width of that zero-quotient gap by delta=0; the original strict
gap geometry forces its width to be POSITIVE. Contradiction.

This exclusion is independent of any translated Boolean hole, dyadic
surplus, Hall expansion or admitted lower-branch capacity theorem.
It is an exact five-point geometric obstruction at the integer strip
endpoint. Its hypotheses are the ORIGINAL planar AngleCap and the
ORIGINAL projective ray cycle, not a synthetic model.
-/

namespace JSP000404Research
open scoped BigOperators

/-- No original centre of any genuinely five-point planar AngleCap
configuration can have ALL THREE possible integer units of projective
quotient mass at the integer scale t=3. The decisive input is strict
positivity of all FOUR genuine projective gaps; no source token,
exterior hole, or all-cardinality conjecture is assumed. -/
theorem five_centre_exact_three_scale_forbids_quotient_sum_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 5)
    (ht : t = 3)
    (hlam : lam = Real.pi / t)
    (i : V) (C : CentreProjectiveCycle hp i)
    (hsum : (∑ r, centreQuotient C t r) = 3) : False := by
  classical
  have hother : Fintype.card (OtherVertex i) = 4 := by
    change Fintype.card {j : V // j ≠ i} = 4
    rw [Fintype.card_subtype_compl (fun j : V => j = i),
      Fintype.card_subtype_eq, hcard]
  have hraylen : C.rays.length = Fintype.card (OtherVertex i) := by
    rw [← List.toFinset_card_of_nodup C.nodup, C.complete]
    simp
  have hgap4 : C.gaps.length = 4 := by
    calc
      C.gaps.length = C.rays.length := C.gaps_length
      _ = Fintype.card (OtherVertex i) := hraylen
      _ = 4 := hother
  have hzero : ∃ r : Fin C.gaps.length, centreQuotient C t r = 0 := by
    by_contra hnone
    push Not at hnone
    have hmin : ∀ r : Fin C.gaps.length, 1 ≤ centreQuotient C t r := by
      intro r
      have hpos := hnone r
      omega
    have hsumlow :
        (∑ _r : Fin C.gaps.length, (1 : ℕ)) ≤
          (∑ r, centreQuotient C t r) := by
      apply Finset.sum_le_sum
      intro r _
      exact hmin r
    have hones :
        (∑ _r : Fin C.gaps.length, (1 : ℕ)) = 4 := by
      simp [hgap4]
    omega
  obtain ⟨r, hqr⟩ := hzero
  have htpos : 0 < t := by rw [ht]; norm_num
  have hlampos : 0 < lam := by rw [hlam]; positivity
  have hgapPos : 0 < C.gaps.get r :=
    centreProjectiveCycle_gaps_pos_of_AngleCap
      hp hcap hlampos i C _ (List.get_mem _ _)
  have hg0 : ∀ j : Fin C.gaps.length, 0 ≤ t * C.gaps.get j := by
    intro j
    exact mul_nonneg htpos.le
      (C.gaps_nonneg (C.gaps.get j) (List.get_mem _ _))
  have hgsum : (∑ j : Fin C.gaps.length, C.gaps.get j) = 1 := by
    rw [← List.sum_ofFn]
    simpa using C.gaps_sum
  have hqsum :
      (∑ j : Fin C.gaps.length, Nat.floor (t * C.gaps.get j)) = 3 := by
    simpa [centreQuotient] using hsum
  have hslack : t * C.gaps.get r ≤ (0 : ℝ) :=
    scaled_zero_floor_gap_le_three_slack
      (fun j : Fin C.gaps.length => C.gaps.get j)
      t 0 (by rw [ht]; norm_num)
      hg0 hgsum hqsum r (by simpa [centreQuotient] using hqr)
  exact (not_le_of_gt (mul_pos htpos hgapPos)) hslack

#print axioms five_centre_exact_three_scale_forbids_quotient_sum_three

end JSP000404Research
