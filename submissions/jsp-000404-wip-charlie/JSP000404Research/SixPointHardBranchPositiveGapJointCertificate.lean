import JSP000404Research.SixPointSeparatedSupportTwo
import JSP000404Research.PositiveGapSeventeenPhase
import Mathlib.Tactic

/-!
# Joint geometric certificate for the six-centre uncompensated top branch

For n>=8, the actual hard six-centre profile with no compensated
top deletion admits BOTH:
* a non-top minimum with exactly two positive quotient coordinates,
  which is non-gaining and has no top-pinned positive-positive
  quotient pair; and
* one common in-period normalized projective phase avoiding ALL
  canonical positive quotient-gap bad arcs of all six centres.

The two witnesses live in precisely the same original geometric
configuration. This packages two kernel-verified independent
necessary conditions and does NOT claim that the combination is
impossible, yields a Boolean hole, or pays global dyadic debt.
-/

namespace JSP000404Research

theorem six_point_uncompensated_top_has_separated_two_and_safe_positive_phase
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn8 : 8 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    ∃ v : V, ∃ hv : v ≠ top,
      positiveSupport (centreQuotient (C v) t) = 2 ∧
      v ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t ∧
      ¬ TopPinnedPositivePair C top v hv t ∧
      ∃ x : ℝ, 0 ≤ x ∧ x < t ∧
        ∀ u : GlobalPositiveGapSlot C t,
          ¬ GlobalCyclicPositiveGapBadAt C t delta u x := by
  obtain ⟨v, hv, htwo, hnotGain, hnotPinned⟩ :=
    exists_separated_support_two_minimum_of_no_compensated_top
      hp hcap C hcard (by omega : 5 ≤ n)
      hdelta0 hdeltaHalf ht hlam top hTop hMin hNoTop
  obtain ⟨x, hx0, hxt, hsafe⟩ :=
    six_point_exists_period_phase_without_positiveGap_bad
      C hn8 hdelta0 hdeltaHalf ht hcard top hTop hMin
  exact ⟨v, hv, htwo, hnotGain, hnotPinned, x, hx0, hxt, hsafe⟩

#print axioms six_point_uncompensated_top_has_separated_two_and_safe_positive_phase

end JSP000404Research
