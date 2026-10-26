import JSP000404Research.PlanarLowSupportCardinalityPacking
import JSP000404Research.HighExponentTransitionPacking
import Mathlib.Tactic

/-!
# Actual original low-support packing with extra costs for support-one layers

The previously verified bound \`card lowSupport <= 2*n\` charges one
strict-support transition quotient per original low-support centre.
However, the verified highTransition_qe_eq_exponent_add_one_of_support_one
shows the transition cost at a support-one centre is *exactly*
one more than its exponent. In particular every exponent-positive
support-one centre consumes at least TWO genuine transition units.

This gives a stricter ORIGINAL AngleCap geometric bound for the
same low-support subfamily. All selected certificates are constructed
from real projective cycles; no synthetic Boolean hole, unused dyadic
credit, or new axiom is asserted.
-/

namespace JSP000404Research
open scoped BigOperators

/-- In any real lower-half strip, low-support original centres consume
one strict-support packing unit apiece, and every support-one centre
with positive exponent consumes at least one ADDITIONAL unit.

The selected index type is literally the subtype of ORIGINAL centres
whose positive quotient support is at most two; high-support centres
are not required to have certificates. -/
theorem planar_weighted_low_support_subfamily_card_le_two_n
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
    let I := {i : V // positiveSupport (centreQuotient (C i) t) ≤ 2}
    Fintype.card I +
      ((Finset.univ : Finset I).filter
        (fun (i : I) =>
          positiveSupport (centreQuotient (C (i : V)) t) = 1 ∧
          1 ≤ centreExponent (C (i : V)) t)).card ≤ 2 * n := by
  classical
  let I : Type _ :=
    {i : V // positiveSupport (centreQuotient (C i) t) ≤ 2}
  let cost : I → Prop := fun r =>
    positiveSupport (centreQuotient (C r) t) = 1 ∧
      1 ≤ centreExponent (C r) t
  have htpos : 0 < t := by
    rw [ht]
    have hnreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    linarith
  have htone : 1 ≤ t := by
    rw [ht]
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  let cert : ∀ r : I,
      HighExponentTransitionIntervalCertificate hp t (r : V) (C r) :=
    fun r => Classical.choose
      (exists_transitionIntervalCertificate_of_support_le_two
        hp hcap htpos htone hlam (r : V) (C r) r.property)
  have hpositive (r : I) : 1 ≤ (cert r).qe := by
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
  have hcost (r : I) :
      1 + (if cost r then (1 : ℕ) else 0) ≤ (cert r).qe := by
    by_cases hr : cost r
    · have heq :
          (cert r).qe = centreExponent (C r) t + 1 :=
        highTransition_qe_eq_exponent_add_one_of_support_one
          (C r) (cert r) hr.1
      simp only [if_pos hr]
      omega
    · simpa only [if_neg hr, add_zero] using hpositive r
  have hsum :
      (∑ r : I, (1 + if cost r then (1 : ℕ) else 0)) ≤
        (∑ r : I, (cert r).qe) := by
    apply Finset.sum_le_sum
    intro r _
    exact hcost r
  have hcardExtra :
      (∑ r : I, if cost r then (1 : ℕ) else 0) =
        ((Finset.univ : Finset I).filter cost).card := by
    rw [← Finset.sum_filter]
    simp
  have hcount :
      (∑ r : I, (1 + if cost r then (1 : ℕ) else 0)) =
        Fintype.card I +
          ((Finset.univ : Finset I).filter cost).card := by
    rw [Finset.sum_add_distrib, hcardExtra]
    simp
  have hresult :
      Fintype.card I +
        ((Finset.univ : Finset I).filter cost).card ≤ 2 * n := by
    omega
  simpa [I, cost] using hresult

#print axioms planar_weighted_low_support_subfamily_card_le_two_n

end JSP000404Research
