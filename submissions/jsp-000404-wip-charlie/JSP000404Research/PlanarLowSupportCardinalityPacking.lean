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

#print axioms planar_low_support_all_centres_card_le_two_n

end JSP000404Research
