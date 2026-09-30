import JSP000404Research.SixPointSupportMultiplicityReduction
import JSP000404Research.SixPointConcreteTopDeletion
import JSP000404Research.SixPointSupportThreeMinimumDeletion
import Mathlib.Tactic

/-!
# Final support-profile reduction after compensated deletions

The six-point third-layer support reduction has three coarse branches:

1. at least four support-three minima;
2. a mixed support-one / support-two pair;
3. a support-two / support-two pair.

Branch (1) already gives a compensated deletion of the sharp top.

For an individual support-three minimum, the non-top deletion machinery gives
another dichotomy:

* middle-hidden pinned shape; or
* a compensated deletion of some minimum.

Therefore, once both kinds of compensated deletion are excluded, the remaining
configuration has a very rigid form:

* the low-support layer contains either a (1,2) pair or a (2,2) pair;
* every support-three minimum that remains is middle-hidden.

This is the clean entry point for the final low-support geometry.
-/

namespace JSP000404Research

open scoped BigOperators

def SixPointNoCompensatedMinimumDeletion
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard3 : 3 ≤ Fintype.card V)
    (top : V)
    (t : ℝ)
    (n : ℕ) : Prop :=
  ∀ deleted : V, deleted ≠ top →
    ¬ (
      2 ^ (n - 1) + 5 * 2 ^ (n - 3)
        ≤
      ∑ v ∈ (Finset.univ.erase deleted : Finset V),
        2 ^ exponentAfterDeleteAt C hcard3 deleted t v
    )

theorem support_three_middle_of_no_compensated_minimum_deletion
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop :
      centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hNoMin :
      SixPointNoCompensatedMinimumDeletion
        C (by rw [hcard]; omega) top t n)
    {i : V}
    (hit : i ≠ top)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = 3) :
    SupportThreePinnedMiddleShape hp hit.symm (C i) := by
  rcases six_point_support_three_middle_or_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
      top hTop hMin hit hsupport
    with hmiddle | ⟨deleted, hdelTop, hcomp⟩
  · exact hmiddle
  · exact False.elim
      ((hNoMin deleted hdelTop) hcomp)

/-- If compensated top deletion is also excluded, the only remaining
support-multiplicity regimes are mixed (1,2) and pure (2,2). -/
theorem six_point_hard_support_profile_reduction
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop :
      centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hNoTop :
      ¬ ∃ good : Finset V,
        good ⊆ (Finset.univ.erase top : Finset V) ∧
        good.card = 4 ∧
        (∀ v ∈ good,
          positiveSupport (centreQuotient (C v) t) = 3))
    (hNoMin :
      SixPointNoCompensatedMinimumDeletion
        C (by rw [hcard]; omega) top t n) :
    (
      (∃ a b : V,
        a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
        positiveSupport (centreQuotient (C a) t) = 1 ∧
        positiveSupport (centreQuotient (C b) t) = 2)
      ∨
      (∃ a b : V,
        a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
        positiveSupport (centreQuotient (C a) t) = 2 ∧
        positiveSupport (centreQuotient (C b) t) = 2)
    )
    ∧
    (∀ i : V, i ≠ top →
      positiveSupport (centreQuotient (C i) t) = 3 →
      SupportThreePinnedMiddleShape hp (show top ≠ i by simpa) (C i)) := by
  classical
  have hprofile :=
    six_point_support_multiplicity_reduction
      hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
      hcard top hTop hMin
  dsimp only at hprofile

  have hnotFour :
      ¬ 4 ≤
        ((Finset.univ.erase top).filter
          (fun v =>
            positiveSupport (centreQuotient (C v) t) = 3)).card := by
    intro hfour
    let good :=
      (Finset.univ.erase top).filter
        (fun v =>
          positiveSupport (centreQuotient (C v) t) = 3)
    have hsub :
        good ⊆ (Finset.univ.erase top : Finset V) :=
      Finset.filter_subset _ _
    obtain ⟨chosen, hchosenSub, hchosenCard⟩ :=
      Finset.exists_subset_card_eq hfour
    have hchosenSupport :
        ∀ v ∈ chosen,
          positiveSupport (centreQuotient (C v) t) = 3 := by
      intro v hv
      have hvGood := hchosenSub hv
      exact (Finset.mem_filter.mp hvGood).2
    exact hNoTop
      ⟨chosen,
        fun v hv => hsub (hchosenSub hv),
        hchosenCard,
        hchosenSupport⟩

  have hlow :
      (∃ a b : V,
        a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
        positiveSupport (centreQuotient (C a) t) = 1 ∧
        positiveSupport (centreQuotient (C b) t) = 2)
      ∨
      (∃ a b : V,
        a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
        positiveSupport (centreQuotient (C a) t) = 2 ∧
        positiveSupport (centreQuotient (C b) t) = 2) := by
    rcases hprofile with hfour | hmixed | htwo
    · exact False.elim (hnotFour hfour)
    · exact Or.inl hmixed
    · exact Or.inr htwo

  refine ⟨hlow, ?_⟩
  intro i hit hsup
  exact support_three_middle_of_no_compensated_minimum_deletion
    hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
    top hTop hMin hNoMin hit hsup

#print axioms SixPointNoCompensatedMinimumDeletion
#print axioms support_three_middle_of_no_compensated_minimum_deletion
#print axioms six_point_hard_support_profile_reduction

end JSP000404Research
