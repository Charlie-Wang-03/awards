import JSP000404Research.AngleCapStrictProjectiveTheta
import JSP000404Research.GeneralSaturatedZeroGapBudget
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Arbitrary-width ACTUAL planar top-layer exclusion at integer scales

For genuinely distinct planar centres satisfying the original positive
AngleCap, EVERY cyclic projective gap is strictly positive. At exact
integer scale t=n, if at least n+2 original vertices are present, each
centre has at least n+1 such positive gaps.

An integer quotient sum equal to n must then contain a ZERO floor
coordinate by elementary counting. The exact original geometric
fractional-remainder identity bounds the scaled zero-quotient gap
by delta=0, contradicting that same genuine strict gap positivity.

Consequently, for n>=2, the original top exponent k=n-1 is impossible
in any genuine n+2-or-more-centre AngleCap configuration at t=n:
k <= n-2 at EVERY actual centre. No exterior-hole payments, Hall
expansion, artificial credits or admitted statements are used.

This is a new unconditional restriction at the EXACT integer endpoint;
it does NOT imply the all-cardinality theorem for arbitrary delta>0.
-/

namespace JSP000404Research
open scoped BigOperators

/-- ORIGINAL AngleCap forbids maximal quotient mass at integer scale
when there are more strictly positive projective gaps than integer
quotient units. All vertices and gaps are actual planar data. -/
theorem planar_exact_integer_many_centres_quotient_mass_lt_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hcard : n + 2 ≤ Fintype.card V)
    (ht : t = (n : ℝ))
    (hlam : lam = Real.pi / t)
    (i : V) (C : CentreProjectiveCycle hp i) :
    (∑ r, centreQuotient C t r) < n := by
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
  have hlt : (∑ r, centreQuotient C t r) < n := by
    by_contra hnot
    have hqle : (∑ r, centreQuotient C t r) ≤ n :=
      centreQuotient_function_sum_le_n
        C n 0 t hn (by norm_num) (by norm_num) (by simpa using ht)
    have hqsum : (∑ r, centreQuotient C t r) = n := by omega
    have hzero :
        ∃ r : Fin C.gaps.length, centreQuotient C t r = 0 := by
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
      exact_mod_cast (show 0 < n by omega)
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
    have hqsum' :
        (∑ j : Fin C.gaps.length, Nat.floor (t * C.gaps.get j)) = n := by
      simpa [centreQuotient] using hqsum
    have hslackRaw :=
      general_saturated_zero_floor_subset_sum_le_slack
        (fun j : Fin C.gaps.length => C.gaps.get j)
        n t (0 : ℝ) (by simpa using ht)
        hg0 hgsum hqsum' ({r} : Finset (Fin C.gaps.length))
        (by
          intro j hj
          have heq : j = r := Finset.mem_singleton.mp hj
          subst j
          simpa [centreQuotient] using hqr)
    have hslack : t * C.gaps.get r ≤ (0 : ℝ) := by
      simpa using hslackRaw
    exact (not_le_of_gt (mul_pos htpos hgapPos)) hslack
  exact hlt

/-- At the exact integer strip endpoint t=n with n>=2, any
n+2-or-more original AngleCap vertices completely exclude the
top exponent n-1. This is a GEOMETRIC fact, independent of a
global source-to-hole allocation. -/
theorem planar_exact_integer_many_centres_exponent_le_n_sub_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 2 ≤ n)
    (hcard : n + 2 ≤ Fintype.card V)
    (ht : t = (n : ℝ))
    (hlam : lam = Real.pi / t)
    (i : V) (C : CentreProjectiveCycle hp i) :
    centreExponent C t ≤ n - 2 := by
  have hqle : (∑ r, centreQuotient C t r) ≤ n :=
    centreQuotient_function_sum_le_n
      C n 0 t (by omega : 1 ≤ n) (by norm_num) (by norm_num)
      (by simpa using ht)
  have hklt : centreExponent C t < n :=
    centreExponent_lt_n C n 0 t
      (by omega : 1 ≤ n) (by norm_num) (by norm_num)
      (by simpa using ht)
  have hnoTop : centreExponent C t ≠ n - 1 := by
    intro htop
    have hdef :
        n - floorExcess (centreQuotient C t) = 1 := by
      change n - centreExponent C t = 1
      omega
    have hqsum := (unit_deficit_structure
      (centreQuotient C t) n hn hqle hdef).2
    have hqstrict :=
      planar_exact_integer_many_centres_quotient_mass_lt_n
        hp hcap (by omega : 1 ≤ n) hcard ht hlam i C
    omega
  omega

#print axioms planar_exact_integer_many_centres_quotient_mass_lt_n
#print axioms planar_exact_integer_many_centres_exponent_le_n_sub_two

end JSP000404Research
