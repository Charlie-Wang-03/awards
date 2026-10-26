import JSP000404Research.PlanarLowSupportCardinalityPacking
import JSP000404Research.PlanarExactIntegerLargeCentreTopExclusion
import Mathlib.Tactic

/-!
# ORIGINAL geometric overcrowding forces a high-support low-exponent centre

The real strict-transition-arc packing theorem certifies that if EVERY
original centre has quotient support <=2, then #centres <=2n.
Consequently, any original configuration with MORE than 2n centres
must have an actual centre with support >=3.

At the INTEGER strip endpoint delta=0, strict positive projective gaps
imply the selected centre's quotient sum is strictly <n provided the
original set has >=n+2 centres. Thus its genuine local exponent
satisfies k<=n-4.

For n=4, >=9 original centres consequently force an actual
exponent-ZERO centre with exactly THREE positive quotient gaps,
each quotient exactly ONE, and total quotient mass THREE.
This is an unconditional constraint on the still-open large-centre
regime. It neither excludes the structure nor pays any Boolean-hole
debt, but turns a large-cardinality counterexample into a rigid
physical projective-gap motif.
-/

namespace JSP000404Research
open scoped BigOperators

/-- If there are more than 2n original planar centres in a genuine
integer strip, some centre has at least THREE positive projective
quotients and local exponent at most n-4. -/
theorem planar_integer_overcrowding_forces_high_support_low_exponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 4 ≤ n)
    (hcard : 2 * n < Fintype.card V)
    (ht : t = (n : ℝ))
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ∃ i : V,
      3 ≤ positiveSupport (centreQuotient (C i) t) ∧
      centreExponent (C i) t ≤ n - 4 := by
  classical
  have hmore : n + 2 ≤ Fintype.card V := by omega
  have hdelta0 : (0 : ℝ) ≤ 0 := by norm_num
  have hdeltaHalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hscale : t = (n : ℝ) + (0 : ℝ) := by simpa using ht
  have hexists :
      ∃ i : V, 3 ≤ positiveSupport (centreQuotient (C i) t) := by
    by_contra hno
    have hlow :
        ∀ i : V, positiveSupport (centreQuotient (C i) t) ≤ 2 := by
      intro i
      by_contra hlarge
      have h3 : 3 ≤ positiveSupport (centreQuotient (C i) t) := by omega
      exact hno ⟨i, h3⟩
    have hbudget :
        Fintype.card V ≤ 2 * n :=
      planar_low_support_all_centres_card_le_two_n
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdeltaHalf hscale hlam C hlow
    omega
  obtain ⟨i, hi⟩ := hexists
  have hmass :
      (∑ r, centreQuotient (C i) t r) < n :=
    planar_exact_integer_many_centres_quotient_mass_lt_n
      hp hcap (by omega : 1 ≤ n) hmore ht hlam i (C i)
  have hdecomp :
      centreExponent (C i) t +
        positiveSupport (centreQuotient (C i) t) =
      ∑ r, centreQuotient (C i) t r := by
    exact floorExcess_add_positiveSupport (centreQuotient (C i) t)
  exact ⟨i, hi, by omega⟩

/-- In n=4 exact integer geometry, >=9 ACTUAL centres force a
genuine exponent-zero centre with support exactly three and
the exact triple-unit quotient profile (sum q = 3). -/
theorem planar_four_integer_nine_centres_forces_zero_three_support
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 9 ≤ Fintype.card V)
    (ht : t = (4 : ℝ))
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ∃ i : V,
      centreExponent (C i) t = 0 ∧
      positiveSupport (centreQuotient (C i) t) = 3 ∧
      (∑ r, centreQuotient (C i) t r) = 3 := by
  obtain ⟨i, hsup, hexp⟩ :=
    planar_integer_overcrowding_forces_high_support_low_exponent
      hp hcap (by decide : 4 ≤ (4 : ℕ))
      (by omega : 2 * (4 : ℕ) < Fintype.card V)
      ht hlam C
  have hmass :
      (∑ r, centreQuotient (C i) t r) < 4 :=
    planar_exact_integer_many_centres_quotient_mass_lt_n
      hp hcap (by decide : 1 ≤ (4 : ℕ))
      (by omega : (4 : ℕ) + 2 ≤ Fintype.card V)
      ht hlam i (C i)
  have hdecomp :
      centreExponent (C i) t +
        positiveSupport (centreQuotient (C i) t) =
      ∑ r, centreQuotient (C i) t r :=
    floorExcess_add_positiveSupport (centreQuotient (C i) t)
  refine ⟨i, ?_, ?_, ?_⟩ <;> omega

#print axioms planar_integer_overcrowding_forces_high_support_low_exponent
#print axioms planar_four_integer_nine_centres_forces_zero_three_support

end JSP000404Research
