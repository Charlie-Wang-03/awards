import JSP000404Research.PlanarExactIntegerLargeCentreTopExclusion
import JSP000404Research.NoTopNextLayerFourCentrePacking
import Mathlib.Tactic

/-!
# Genuine integer-scale second-layer support rigidity, arbitrary width

At exact scale t=n with n>=3, an original configuration with >=n+2
centres has quotient sum STRICTLY less than n at every centre, by
the previously kernel-certified strict projective gap obstruction.

A genuine centre of second-layer exponent k=n-2 therefore has
positive support ONE, not TWO. This uses no conditional Hall expansion
or Boolean hole payment: k+support = quotient sum, and support=0
would imply k=0, inconsistent with n>=3 and k=n-2.

A companion of exponent k>=n-3 has support at most TWO. Combining
with the independently certified original AngleCap transition-packing
lemma rules out three distinct second-layer centres and a distinct
companion whose exponent is at least n-3.

All statements use the actual original projective cycles and planar
AngleCap; no global capacity theorem is assumed.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Every n-2 exponent original centre has EXACTLY ONE positive
projective quotient at the exact integer scale, once the original
centre count is at least n+2. -/
theorem planar_integer_many_centres_second_layer_support_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hcard : n + 2 ≤ Fintype.card V)
    (ht : t = (n : ℝ))
    (hlam : lam = Real.pi / t)
    (i : V) (C : CentreProjectiveCycle hp i)
    (hk : centreExponent C t = n - 2) :
    positiveSupport (centreQuotient C t) = 1 := by
  have hmass :
      (∑ r, centreQuotient C t r) < n :=
    planar_exact_integer_many_centres_quotient_mass_lt_n
      hp hcap (by omega : 1 ≤ n) hcard ht hlam i C
  have hdecomp :
      centreExponent C t + positiveSupport (centreQuotient C t) =
        ∑ r, centreQuotient C t r := by
    exact floorExcess_add_positiveSupport (centreQuotient C t)
  have hsupportPos : 0 < positiveSupport (centreQuotient C t) := by
    by_contra hnot
    have hzero : positiveSupport (centreQuotient C t) = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have hqzero : ∀ r, centreQuotient C t r = 0 :=
      positiveSupport_eq_zero_imp (centreQuotient C t) hzero
    have hkzero : centreExponent C t = 0 := by
      unfold centreExponent floorExcess
      simp [hqzero]
    omega
  omega

/-- A distinct companion at exponent at least n-3 consumes at most
TWO positive quotient gaps at the actual integer scale. -/
theorem planar_integer_many_centres_third_layer_support_le_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hcard : n + 2 ≤ Fintype.card V)
    (ht : t = (n : ℝ))
    (hlam : lam = Real.pi / t)
    (i : V) (C : CentreProjectiveCycle hp i)
    (hk : n - 3 ≤ centreExponent C t) :
    positiveSupport (centreQuotient C t) ≤ 2 := by
  have hmass :
      (∑ r, centreQuotient C t r) < n :=
    planar_exact_integer_many_centres_quotient_mass_lt_n
      hp hcap (by omega : 1 ≤ n) hcard ht hlam i C
  have hdecomp :
      centreExponent C t + positiveSupport (centreQuotient C t) =
        ∑ r, centreQuotient C t r := by
    exact floorExcess_add_positiveSupport (centreQuotient C t)
  omega

/-- REAL AngleCap integer-strip packing: three distinct original
second-layer centres cannot coexist with any fourth original centre
of exponent at least n-3 when |V|>=n+2. This is a genuine geometric
four-owner exclusion, rather than an abstract numerical debt identity. -/
theorem planar_integer_no_three_next_with_third_layer_companion
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hcard : n + 2 ≤ Fintype.card V)
    (ht : t = (n : ℝ))
    (hlam : lam = Real.pi / t)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hs : centreExponent (C s) t = n - 2)
    (ha : centreExponent (C a) t = n - 2)
    (hb : centreExponent (C b) t = n - 2)
    (hc : n - 3 ≤ centreExponent (C c) t) : False := by
  have hss :=
    planar_integer_many_centres_second_layer_support_one
      hp hcap hn hcard ht hlam s (C s) hs
  have haa :=
    planar_integer_many_centres_second_layer_support_one
      hp hcap hn hcard ht hlam a (C a) ha
  have hbb :=
    planar_integer_many_centres_second_layer_support_one
      hp hcap hn hcard ht hlam b (C b) hb
  have hcc :=
    planar_integer_many_centres_third_layer_support_le_two
      hp hcap hn hcard ht hlam c (C c) hc
  have hdelta0 : 0 ≤ (0 : ℝ) := by norm_num
  have hdeltaHalf : (0 : ℝ) < 1 / 2 := by norm_num
  have ht0 : t = (n : ℝ) + (0 : ℝ) := by simpa using ht
  exact no_three_next_support_one_with_fourth_low_support
    hp hcap hn hdelta0 hdeltaHalf ht0 hlam
    hsa hsb hsc hab hac hbc
    (C s) (C a) (C b) (C c) hs ha hb hss haa hbb hcc

#print axioms planar_integer_many_centres_second_layer_support_one
#print axioms planar_integer_many_centres_third_layer_support_le_two
#print axioms planar_integer_no_three_next_with_third_layer_companion

end JSP000404Research
