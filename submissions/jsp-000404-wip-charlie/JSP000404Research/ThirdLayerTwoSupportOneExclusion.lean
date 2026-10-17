import JSP000404Research.DeficitThreeSupportOneGeometry
import JSP000404Research.NoTopTwoNextMultiplicity
import Mathlib.Tactic

/-!
# Two exact n-3 support-one centres cannot surround a sharp top for n>=5

The certified deficit-three/support-one common-signed interval forces
angle(s,a,b) <= (2+delta)*lambda at centre a.
With a sharp vertex s the *other* such centre b sees the complementary
angle(s,b,a) >= (n-2-delta)*lambda.
If b itself is also n-3 support-one, the same common-signed interval
forces angle(s,b,a) <= (2+delta)*lambda, impossible for n>=5,
delta<1/2, lambda>0.

This excludes an ACTUAL planar geometric configuration without any
hypothetical true-hole payment or added cardinality premise.
-/

namespace JSP000404Research

open Real

/-- A real sharp centre cannot coexist with TWO distinct n-3
support-one centres in the strict lower branch when n>=5. -/
theorem no_two_third_support_one_around_sharp_n_ge_five
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hs : SharpAt p delta lam s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hA : centreExponent Ca t = n - 3)
    (hB : centreExponent Cb t = n - 3)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 1) :
    False := by
  have hlarge :=
    sharp_and_deficit_three_support_one_force_large_outer_angle
      hp hcap (by omega : 4 ≤ n) hdelta0 ht hlam
      hsa hsb hab hs Ca hA hsupA
  have hsmall :=
    deficit_three_support_one_all_angles_le
      hp hcap (by omega : 4 ≤ n) hdelta0 ht hlam
      Cb hB hsupB s a hsb hab hsa
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hncast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    simpa only [Nat.cast_ofNat] using
      (Nat.cast_sub (by omega : 2 ≤ n) :
        ((n - 2 : ℕ) : ℝ) = (n : ℝ) - ((2 : ℕ) : ℝ))
  have hnreal : (5 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hcoeff : 2 + delta < (n : ℝ) - 2 - delta := by
    linarith
  have hstrict :
      (2 + delta) * lam < ((n : ℝ) - 2 - delta) * lam :=
    mul_lt_mul_of_pos_right hcoeff hlampos
  rw [hncast] at hlarge
  linarith

/-- Deduce the same exclusion from an ACTUAL top exponent n-1,
rather than passing a separate sharpness axiom. -/
theorem no_top_with_two_third_support_one_n_ge_five
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hs : centreExponent (C s) t = n - 1)
    (hA : centreExponent (C a) t = n - 3)
    (hB : centreExponent (C b) t = n - 3)
    (hsupA : positiveSupport (centreQuotient (C a) t) = 1)
    (hsupB : positiveSupport (centreQuotient (C b) t) = 1) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have hsharp : SharpAt p delta lam s :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n) hdelta0 hdelta1 ht hlam
      s (C s) hs
  exact no_two_third_support_one_around_sharp_n_ge_five
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hab hsharp (C a) (C b) hA hB hsupA hsupB

/-- Actual geometric multiplicity bound: with a true top n-1 centre
in the lower branch and n>=5, at most ONE OTHER centre may
simultaneously have exponent n-3 and quotient support one. -/
theorem top_third_support_one_count_le_one_n_ge_five
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hs : centreExponent (C s) t = n - 1) :
    ((Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧
        centreExponent (C i) t = n - 3 ∧
        positiveSupport (centreQuotient (C i) t) = 1)).card ≤ 1 := by
  classical
  let S : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧
        centreExponent (C i) t = n - 3 ∧
        positiveSupport (centreQuotient (C i) t) = 1)
  by_contra hnot
  change ¬ S.card ≤ 1 at hnot
  have hgt : 1 < S.card := by omega
  rcases Finset.one_lt_card.mp hgt with ⟨a, ha, b, hb, hab⟩
  have ha' : a ≠ s ∧
      centreExponent (C a) t = n - 3 ∧
      positiveSupport (centreQuotient (C a) t) = 1 := by
    simpa [S] using ha
  have hb' : b ≠ s ∧
      centreExponent (C b) t = n - 3 ∧
      positiveSupport (centreQuotient (C b) t) = 1 := by
    simpa [S] using hb
  exact no_top_with_two_third_support_one_n_ge_five
    hp hcap hn hdelta0 hdeltaHalf ht hlam C
    ha'.1.symm hb'.1.symm hab
    hs ha'.2.1 hb'.2.1 ha'.2.2 hb'.2.2

#print axioms no_two_third_support_one_around_sharp_n_ge_five
#print axioms no_top_with_two_third_support_one_n_ge_five
#print axioms top_third_support_one_count_le_one_n_ge_five

end JSP000404Research
