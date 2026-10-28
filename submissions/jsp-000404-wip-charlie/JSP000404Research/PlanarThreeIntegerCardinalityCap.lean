import JSP000404Research.PlanarExactIntegerLargeCentreTopExclusion
import JSP000404Research.SupportLeTwoTransitionInterval
import JSP000404Research.HighExponentTransitionPacking
import Mathlib.Tactic

/-!
# Real AngleCap forces at most six ORIGINAL points at exact n=3 scale

At t=3, lambda=pi/3, with at least five original plane centres,
the kernel-checked strict-projective-gap obstruction implies that
every centre has total projective integer quotient mass <=2.
Thus every centre has at most two positive quotient slots.

The existing TRUE geometric transition-interval constructor gives
every ORIGINAL centre a strictly POSITIVE transition quotient.
The existing TRUE global strict-support-arc packing says the total
of these selected quotients is <=2*n=6. It follows, without a
synthetic hole, source-slot approximation, or arbitrary matching
hypothesis, that there are at most SIX original centres.

This is much stronger than the previous 5- and 6-centre profile
censuses: it excludes ALL larger original n=3 configurations at
the exact integer endpoint.
-/

namespace JSP000404Research

open scoped BigOperators

/-- In an actual planar configuration of at least five original points
satisfying AngleCap at t=3, each original centre has at most TWO
positive quotient slots, as a direct consequence of the genuine
strict-gap integer mass obstruction. -/
theorem planar_three_integer_many_centres_support_le_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (hcard5 : 5 ≤ Fintype.card V)
    (ht : t = (3 : ℝ))
    (hlam : lam = Real.pi / t)
    (i : V) (C : CentreProjectiveCycle hp i) :
    positiveSupport (centreQuotient C t) ≤ 2 := by
  have hqsum : (∑ r, centreQuotient C t r) < 3 :=
    planar_exact_integer_many_centres_quotient_mass_lt_n
      hp hcap (by decide : 1 ≤ (3 : ℕ)) hcard5 ht hlam i C
  have hsplit :=
    floorExcess_add_positiveSupport (centreQuotient C t)
  omega

/-- Real global AngleCap transition-arc packing proves that at the
exact n=3 integer endpoint the original finite point set can contain
AT MOST six centres, unconditionally. -/
theorem planar_three_integer_card_le_six_of_card_ge_five
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (hcard5 : 5 ≤ Fintype.card V)
    (ht : t = (3 : ℝ))
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    Fintype.card V ≤ 6 := by
  classical
  have htpos : 0 < t := by rw [ht]; norm_num
  have htone : 1 ≤ t := le_of_lt (by rw [ht]; norm_num)
  have hsupport : ∀ i : V,
      positiveSupport (centreQuotient (C i) t) ≤ 2 := by
    intro i
    exact planar_three_integer_many_centres_support_le_two
      hp hcap hcard5 ht hlam i (C i)
  let cert : ∀ i : V,
      HighExponentTransitionIntervalCertificate hp t i (C i) :=
    fun i => Classical.choose
      (exists_transitionIntervalCertificate_of_support_le_two
        hp hcap htpos htone hlam i (C i) (hsupport i))
  have hpositive : ∀ i : V, 1 ≤ (cert i).qe := by
    intro i
    have hi :
        (cert i).qe ≠ 0 :=
      Classical.choose_spec
        (exists_transitionIntervalCertificate_of_support_le_two
          hp hcap htpos htone hlam i (C i) (hsupport i))
    exact Nat.one_le_iff_ne_zero.mpr hi
  have hpack : (∑ i : V, (cert i).qe) ≤ 2 * (3 : ℕ) := by
    exact highTransition_quotient_sum_le_two_n
      hp (by decide : 1 ≤ (3 : ℕ))
      (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by simpa using ht)
      (fun i : V => i) (by intro _ _ h; exact h)
      C cert
  have hones : (∑ _i : V, (1 : ℕ)) ≤
      (∑ i : V, (cert i).qe) := by
    apply Finset.sum_le_sum
    intro i _
    exact hpositive i
  have honesEq : (∑ _i : V, (1 : ℕ)) = Fintype.card V := by simp
  omega

/-- The arbitrary-cardinality form: original geometric AngleCap at
t=3 actually prohibits SEVEN or more planar centres. The cases
with <=4 centres are automatic; for >=5 centres this is the true
transition-packing conclusion. -/
theorem planar_three_integer_card_le_six
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : t = (3 : ℝ))
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    Fintype.card V ≤ 6 := by
  by_cases h5 : 5 ≤ Fintype.card V
  · exact planar_three_integer_card_le_six_of_card_ge_five
      hp hcap h5 ht hlam C
  · omega

#print axioms planar_three_integer_many_centres_support_le_two
#print axioms planar_three_integer_card_le_six_of_card_ge_five
#print axioms planar_three_integer_card_le_six

end JSP000404Research
