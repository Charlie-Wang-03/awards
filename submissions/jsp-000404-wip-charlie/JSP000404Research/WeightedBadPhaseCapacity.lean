import JSP000404Research.WeightedHansel
import Mathlib.Tactic

/-!
# Weighted bad-phase tolerance

The standard (n+1)-band partial code need not meet the exact local Sendov
deficit at every centre.  The one-long-spacing geometry gives the weaker
pointwise bound

  active(v) <= (n - k(v)) + 1.

Call v bad when active(v) is strictly larger than n-k(v).  Then it is exactly
one over budget.  In the weighted Hansel sum,

* a good centre of exponent k contributes at least 2^(k+1);
* a bad centre contributes at least 2^k.

Thus, if

  W = sum_v 2^k(v),
  B = sum_{bad v} 2^k(v),

weighted Hansel implies

  2 W <= 2^(n+1) + B.

Consequently B <= 1 already forces W <= 2^n.  Geometrically, it is enough to
find one phase at which every positive-exponent centre is good and at most one
zero-exponent centre is bad.  This is strictly weaker than requiring a phase
where every centre is good.
-/

namespace JSP000404Research

open scoped BigOperators

def badPhaseWeight
    {V : Type*} [Fintype V]
    (n : ℕ) (exponent active : V → ℕ) : ℕ :=
  ∑ v, if n - exponent v < active v then 2 ^ exponent v else 0

theorem two_mul_dyadic_le_hansel_add_badWeight
    {V : Type*} [Fintype V]
    (n : ℕ)
    (exponent active : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, active v ≤ n - exponent v + 1) :
    2 * (∑ v, 2 ^ exponent v) ≤
      (∑ v, 2 ^ (n + 1 - active v)) +
        badPhaseWeight n exponent active := by
  have hpoint :
      ∀ v : V,
        2 * 2 ^ exponent v ≤
          2 ^ (n + 1 - active v) +
            (if n - exponent v < active v
             then 2 ^ exponent v else 0) := by
    intro v
    by_cases hbad : n - exponent v < active v
    · have hact :
          active v = n - exponent v + 1 := by
        have hup := honeLoss v
        omega
      have hsub :
          n + 1 - active v = exponent v := by
        rw [hact]
        have hk := hexp v
        omega
      rw [if_pos hbad, hsub]
      omega
    · have hgood :
          active v ≤ n - exponent v := by
        omega
      have hpowExp :
          exponent v + 1 ≤ n + 1 - active v := by
        have hk := hexp v
        omega
      have hpow :
          2 ^ (exponent v + 1) ≤
            2 ^ (n + 1 - active v) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hpowExp
      rw [if_neg hbad]
      rw [pow_succ] at hpow
      simpa [Nat.mul_comm] using hpow
  have hsum :=
    Finset.sum_le_sum
      (fun v (_hv : v ∈ (Finset.univ : Finset V)) => hpoint v)
  simpa [badPhaseWeight, Finset.mul_sum, Finset.sum_add_distrib] using hsum

theorem dyadic_capacity_of_badPhaseWeight_le_one
    {V : Type*} [Fintype V]
    (n : ℕ)
    (exponent active : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, active v ≤ n - exponent v + 1)
    (hHansel :
      (∑ v, 2 ^ (n + 1 - active v)) ≤ 2 ^ (n + 1))
    (hbad :
      badPhaseWeight n exponent active ≤ 1) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  have htwo :=
    two_mul_dyadic_le_hansel_add_badWeight
      n exponent active hexp honeLoss
  have hbound :
      2 * (∑ v, 2 ^ exponent v) ≤
        2 ^ (n + 1) + 1 := by
    omega
  rw [pow_succ] at hbound
  omega

/-- Equivalent structural criterion: if every bad centre has exponent zero and
there is at most one bad centre, then the bad dyadic mass is at most one. -/
theorem badPhaseWeight_le_one_of_bad_zero_unique
    {V : Type*} [Fintype V]
    (n : ℕ)
    (exponent active : V → ℕ)
    (hzero :
      ∀ v, n - exponent v < active v → exponent v = 0)
    (huniq :
      ∀ v w,
        n - exponent v < active v →
        n - exponent w < active w →
        v = w) :
    badPhaseWeight n exponent active ≤ 1 := by
  classical
  let S : Finset V :=
    Finset.univ.filter
      (fun v => n - exponent v < active v)
  have hcard : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    have hvbad :
        n - exponent v < active v := by
      simpa [S] using hv
    have hwbad :
        n - exponent w < active w := by
      simpa [S] using hw
    exact huniq v w hvbad hwbad
  have hweight :
      badPhaseWeight n exponent active = S.card := by
    unfold badPhaseWeight
    rw [← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    have hvbad :
        n - exponent v < active v := by
      simpa [S] using hv
    simp [hzero v hvbad]
  rw [hweight]
  exact hcard

#print axioms two_mul_dyadic_le_hansel_add_badWeight
#print axioms dyadic_capacity_of_badPhaseWeight_le_one
#print axioms badPhaseWeight_le_one_of_bad_zero_unique

end JSP000404Research
