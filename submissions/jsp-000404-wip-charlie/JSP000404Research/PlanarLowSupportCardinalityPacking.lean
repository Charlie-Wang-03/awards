import JSP000404Research.SupportLeTwoTransitionInterval
import JSP000404Research.HighExponentTransitionPacking
import Mathlib.Tactic

/-!
# SOURCE-NATIVE all-width cardinality bound for genuine low-support geometry

Given the ORIGINAL AngleCap geometry and actual CentreProjectiveCycle
for every ORIGINAL vertex, suppose all local positive quotient supports
are <=2 at scale t=n+delta (0<=delta<1/2).
The certified support-two transition decomposition produces for
EVERY original vertex a transition interval with positive integer
quotient qe >=1, and the global disjoint strict-support arc packing
says SUM of selected qe <=2n. Hence the number of ORIGINAL vertices
is at most 2n.

No geometrically invalid assumption about coverage or completion
Boolean cubes is introduced; this is a full original-plane geometric
result conditional ONLY on the explicit low-support regime.
Applications must PROVE low-support from their local geometric data,
not assume it automatically for all n or all delta.
-/

namespace JSP000404Research
open scoped BigOperators

/-- Each original-plane centre with support <=2 consumes at least
one genuine unit of the shared strict-transition-arc packing bound.
For any finite set of ORIGINAL centres this gives card <=2n. -/
theorem planar_low_support_all_centres_card_le_two_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hsupport : ∀ i : V,
      positiveSupport (centreQuotient (C i) t) ≤ 2) :
    Fintype.card V ≤ 2 * n := by
  classical
  have htpos : 0 < t := by
    rw [ht]
    have hnreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    linarith
  have htone : 1 ≤ t := by
    rw [ht]
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  let cert : ∀ i : V,
      HighExponentTransitionIntervalCertificate hp t i (C i) :=
    fun i => Classical.choose
      (exists_transitionIntervalCertificate_of_support_le_two
        hp hcap htpos htone hlam i (C i) (hsupport i))
  have hpositive : ∀ i : V, 1 ≤ (cert i).qe := by
    intro i
    have hi : (cert i).qe ≠ 0 :=
      Classical.choose_spec
        (exists_transitionIntervalCertificate_of_support_le_two
          hp hcap htpos htone hlam i (C i) (hsupport i))
    exact Nat.one_le_iff_ne_zero.mpr hi
  have hpack :
      (∑ i : V, (cert i).qe) ≤ 2 * n :=
    highTransition_quotient_sum_le_two_n
      hp hn hdelta0 hdeltaHalf ht
      (fun i : V => i) (by intro a b h; exact h)
      C cert
  have hones :
      (∑ _i : V, (1 : ℕ)) ≤
        (∑ i : V, (cert i).qe) := by
    apply Finset.sum_le_sum
    intro i _
    exact hpositive i
  have hcard : (∑ _i : V, (1 : ℕ)) = Fintype.card V := by
    simp
  omega

/-- The strict-support arc packing bound applies to the SUBFAMILY of
    original centres with quotient support at most two, even if all
    other original centres have high support. This strengthens the
    whole-configuration low-support implication above. -/
theorem planar_low_support_subfamily_card_le_two_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    Fintype.card
      {i : V // positiveSupport (centreQuotient (C i) t) ≤ 2} ≤ 2 * n := by
  classical
  let I : Type _ :=
    {i : V // positiveSupport (centreQuotient (C i) t) ≤ 2}
  have htpos : 0 < t := by
    rw [ht]
    have hnreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    linarith
  have htone : 1 ≤ t := by
    rw [ht]
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    linarith
  let cert : ∀ r : I,
      HighExponentTransitionIntervalCertificate hp t (r : V) (C r) :=
    fun r => Classical.choose
      (exists_transitionIntervalCertificate_of_support_le_two
        hp hcap htpos htone hlam (r : V) (C r) r.property)
  have hpositive : ∀ r : I, 1 ≤ (cert r).qe := by
    intro r
    have hr : (cert r).qe ≠ 0 :=
      Classical.choose_spec
        (exists_transitionIntervalCertificate_of_support_le_two
          hp hcap htpos htone hlam (r : V) (C r) r.property)
    exact Nat.one_le_iff_ne_zero.mpr hr
  have hinj : Function.Injective (fun r : I => (r : V)) := by
    intro a b hab
    exact Subtype.ext hab
  have hpack : (∑ r : I, (cert r).qe) ≤ 2 * n :=
    highTransition_quotient_sum_le_two_n
      hp hn hdelta0 hdeltaHalf ht
      (fun r : I => (r : V)) hinj
      (fun r : I => C r) cert
  have hones :
      (∑ _r : I, (1 : ℕ)) ≤ (∑ r : I, (cert r).qe) := by
    apply Finset.sum_le_sum
    intro r _
    exact hpositive r
  have hcard : (∑ _r : I, (1 : ℕ)) = Fintype.card I := by
    simp
  change Fintype.card I ≤ 2 * n
  omega

#print axioms planar_low_support_subfamily_card_le_two_n

#print axioms planar_low_support_all_centres_card_le_two_n

end JSP000404Research
