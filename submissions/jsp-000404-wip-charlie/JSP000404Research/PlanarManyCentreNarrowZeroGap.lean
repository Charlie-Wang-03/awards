import JSP000404Research.AngleCapStrictProjectiveTheta
import JSP000404Research.GeneralSaturatedZeroGapBudget
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Any genuine saturated many-centre projective quotient requires a NARROW gap

Unlike the exact-integer-scale corollary, this statement is UNCONDITIONAL
for all 0 <= delta < 1, arbitrary n, and at least n+2 original vertices.

The original AngleCap forces strictly positive projective gaps. At each
centre there are then at least n+1 such gaps. A quotient floor sum of n
must have at least ONE zero-quotient coordinate, otherwise n+1 positive
integers would sum to at most n. The exact original fractional remainder
budget forces this TRUE gap to satisfy t*gap <= delta.

In particular, an original top exponent n-1 at n>=2 has quotient
sum n by the already-certified unit-deficit theorem, so it forces one
genuinely POSITIVE, but DELTA-NARROW, original projective gap.

This supplies a concrete geometric target in the still-open positive
delta root branch. It neither manufactures a true Boolean hole nor
proves global eight-class source payment.
-/

namespace JSP000404Research
open scoped BigOperators

/-- Original many-centre high quotient saturation forces the EXISTENCE
of a strictly positive original projective gap with zero integer floor
and scaled width bounded by the ACTUAL strip remainder delta. -/
theorem planar_many_centres_saturated_quotient_forces_narrow_gap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hcard : n + 2 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V) (C : CentreProjectiveCycle hp i)
    (hsum : (∑ r, centreQuotient C t r) = n) :
    ∃ r : Fin C.gaps.length,
      centreQuotient C t r = 0 ∧
      0 < C.gaps.get r ∧ t * C.gaps.get r ≤ delta := by
  classical
  have hother :
      Fintype.card (OtherVertex i) = Fintype.card V - 1 := by
    change Fintype.card {j : V // j ≠ i} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl (fun j : V => j = i),
      Fintype.card_subtype_eq]
  have hraylen : C.rays.length = Fintype.card (OtherVertex i) := by
    rw [← List.toFinset_card_of_nodup C.nodup, C.complete]
    simp
  have hgapmany : n + 1 ≤ C.gaps.length := by
    rw [C.gaps_length, hraylen, hother]
    omega
  have hzero : ∃ r : Fin C.gaps.length, centreQuotient C t r = 0 := by
    by_contra hnone
    push Not at hnone
    have hmin : ∀ r : Fin C.gaps.length,
        1 ≤ centreQuotient C t r := by
      intro r
      have hne := hnone r
      omega
    have hsumlow :
        (∑ _r : Fin C.gaps.length, (1 : ℕ)) ≤
          (∑ r, centreQuotient C t r) := by
      apply Finset.sum_le_sum
      intro r _
      exact hmin r
    have hones :
        (∑ _r : Fin C.gaps.length, (1 : ℕ)) = C.gaps.length := by
      simp
    omega
  obtain ⟨r, hqr⟩ := hzero
  have htpos : 0 < t := by
    rw [ht]
    have hnreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    linarith
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
      (∑ j : Fin C.gaps.length, Nat.floor (t * C.gaps.get j)) = n := by
    simpa [centreQuotient] using hsum
  have hslackRaw :=
    general_saturated_zero_floor_subset_sum_le_slack
      (fun j : Fin C.gaps.length => C.gaps.get j)
      n t delta ht hg0 hgsum hqsum ({r} : Finset (Fin C.gaps.length))
      (by
        intro j hj
        have heq : j = r := Finset.mem_singleton.mp hj
        subst j
        simpa [centreQuotient] using hqr)
  have hslack : t * C.gaps.get r ≤ delta := by
    simpa using hslackRaw
  exact ⟨r, hqr, hgapPos, hslack⟩

/-- At arbitrary strictly subunit remainder delta, an ORIGINAL top
exponent k=n-1 in a genuine n+2-or-more-centre AngleCap set forces
a real noncollinear projective gap of positive size <= delta/t.
This is a new direct geometric necessary condition, not payment. -/
theorem planar_many_centres_top_exponent_forces_positive_narrow_gap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 2 ≤ n)
    (hcard : n + 2 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V) (C : CentreProjectiveCycle hp i)
    (htop : centreExponent C t = n - 1) :
    ∃ r : Fin C.gaps.length,
      centreQuotient C t r = 0 ∧
      0 < C.gaps.get r ∧ t * C.gaps.get r ≤ delta := by
  have hqle : (∑ r, centreQuotient C t r) ≤ n :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n) hdelta0 hdelta1 ht
  have hdef :
      n - floorExcess (centreQuotient C t) = 1 := by
    change n - centreExponent C t = 1
    omega
  have hqsum := (unit_deficit_structure
    (centreQuotient C t) n hn hqle hdef).2
  exact planar_many_centres_saturated_quotient_forces_narrow_gap
    hp hcap (by omega : 1 ≤ n) hcard hdelta0 ht hlam i C hqsum

#print axioms planar_many_centres_saturated_quotient_forces_narrow_gap
#print axioms planar_many_centres_top_exponent_forces_positive_narrow_gap

end JSP000404Research
