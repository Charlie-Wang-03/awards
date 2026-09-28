import JSP000404Research.SixPointSupportTwoDeletionReduction
import JSP000404Research.SixPointSeparatedSupportTwo
import Mathlib.Tactic

/-!
# No positive-positive ray at a separated support-two hard centre

Under no compensated minimum deletion, a positive-positive ray at any minimum
centre must point to the sharp top.

For a separated support-two centre, the sharp-top ray is not positive-positive
either.

Hence *no* ray at that centre can be flanked by positive cyclic quotients.
This is the position-free hard-branch form needed for the final five-cycle
analysis.
-/

namespace JSP000404Research

theorem no_positive_positive_ray_at_separated_support_two
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 3 ≤ n)
    (ht0 : 0 ≤ t)
    (top : V)
    (hTop :
      centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hNoMin :
      SixPointNoCompensatedMinimumDeletion
        C (by rw [hcard]; omega) top t n)
    {i r : V}
    (hit : i ≠ top)
    (hir : i ≠ r)
    (hsep :
      ¬ TopPinnedPositivePair C top i hit t)
    (pre post : List (OtherVertex i))
    (hsplit :
      (C i).rays =
        pre ++ deletedParentRay r i hir :: post)
    (qOut qIn : ℕ)
    (qmid : List ℕ)
    (hqrot :
      (quotientList t (C i).gaps).rotate pre.length =
        qOut :: qmid ++ [qIn])
    (hOut : 1 ≤ qOut)
    (hIn : 1 ≤ qIn) :
    False := by
  by_cases hrt : r = top
  · subst r
    apply hsep
    exact ⟨pre, post, qOut, qIn, qmid,
      hsplit, hqrot, hOut, hIn⟩
  · exact no_nonTop_positive_positive_ray_of_no_compensated_minimum_deletion
      C hcard hn ht0 top hTop hMin hNoMin
      hit hrt hir
      pre post hsplit qOut qIn qmid hqrot hOut hIn

#print axioms no_positive_positive_ray_at_separated_support_two

end JSP000404Research
