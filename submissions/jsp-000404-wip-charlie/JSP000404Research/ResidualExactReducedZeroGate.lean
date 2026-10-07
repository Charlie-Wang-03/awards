import JSP000404Research.ResidualSafeCommonInactiveCapacity
import Mathlib.Tactic

/-!
# Exact no-active-safe pairs: paid or reduced-zero

Let d be the common-inactive dimension of an exact--exact no-active-safe
overlap pair.

Exact projected budget gives exponent = projectedFree at each endpoint, while
the common-inactive set is contained in each endpoint's retained-inactive set.
Hence d is at most both exponents.

Therefore exactly one of the following happens:

* both reduced exponents are positive, and the existing reduced dyadic
  capacity theorem pays the pair;
* the left reduced exponent is zero;
* the right reduced exponent is zero.

This is the recursion gate needed after a stationary full-blocker rematch:
exact--exact alone is not recursive.  A descendant can recurse only if it
again hits a reduced-zero equality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exact_noActiveSafe_paid_or_reducedZero
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v) :
    (
      2 ^ exponent u + 2 ^ exponent v
        ≤
      2 ^
        (n -
          ((incomingRetained C v).card +
           (outgoingRetained C u).card))
    )
    ∨
    exponent u = (commonInactiveRetained C u v).card
    ∨
    exponent v = (commonInactiveRetained C u v).card := by
  let d := (commonInactiveRetained C u v).card

  have hdUFree :
      d ≤ projectedFree C u := by
    have hsub :
        commonInactiveRetained C u v ⊆
          retainedInactive C u := by
      intro c hc
      apply (mem_retainedInactive C u c).2
      exact (mem_commonInactiveRetained C u v c).1 hc |>.1
    have hcard := Finset.card_le_card hsub
    rw [retainedInactive_card] at hcard
    exact hcard

  have hdVFree :
      d ≤ projectedFree C v := by
    have hsub :
        commonInactiveRetained C u v ⊆
          retainedInactive C v := by
      intro c hc
      apply (mem_retainedInactive C v c).2
      exact (mem_commonInactiveRetained C u v c).1 hc |>.2
    have hcard := Finset.card_le_card hsub
    rw [retainedInactive_card] at hcard
    exact hcard

  have hdU : d ≤ exponent u := by
    rw [huSat]
    exact hdUFree

  have hdV : d ≤ exponent v := by
    rw [hvSat]
    exact hdVFree

  by_cases huPos : d < exponent u
  · by_cases hvPos : d < exponent v
    · left
      exact
        noActiveSafe_saturated_positiveReduced_pair_dyadic_capacity
          C exponent hno huBase hvBase
          huSat hvSat huPos hvPos
    · right
      right
      dsimp [d] at hdV hvPos ⊢
      omega
  · right
    left
    dsimp [d] at hdU huPos ⊢
    omega

#print axioms exact_noActiveSafe_paid_or_reducedZero

end OrderedEdgeColoring
end JSP000404Research
