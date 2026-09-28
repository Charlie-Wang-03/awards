import JSP000404Research.CyclicPositiveRayDeletionGain
import JSP000404Research.SixPointMinimumDeletionWeight
import JSP000404Research.SixPointSupportThreeMinimumDeletion
import JSP000404Research.SixPointHardSupportReduction
import Mathlib.Tactic

/-!
# Non-top adjacent-positive rays are forbidden in the hard six-point branch

At any surviving minimum centre i, if a non-top ray i--r is flanked by two
positive cyclic quotient gaps, deleting r raises the exponent at i by one.
In the six-point 1+5 profile this one-unit gain exactly compensates deleting
the minimum r.

Therefore under SixPointNoCompensatedMinimumDeletion, no non-top ray of a
minimum centre can be flanked by two positive quotient gaps.

For a support-two centre this means: if its two positive cyclic gaps are
adjacent, their common ray must be the sharp top ray.
-/

namespace JSP000404Research

open scoped BigOperators

theorem six_point_nonTop_positive_positive_ray_gives_compensated_deletion
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 3 ≤ n)
    (ht0 : 0 ≤ t)
    (top i deleted : V)
    (hit : i ≠ top)
    (hdelTop : deleted ≠ top)
    (hir : i ≠ deleted)
    (hTop :
      centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (pre post : List (OtherVertex i))
    (hsplit :
      (C i).rays =
        pre ++ deletedParentRay deleted i hir :: post)
    (qOut qIn : ℕ)
    (qmid : List ℕ)
    (hqrot :
      (quotientList t (C i).gaps).rotate pre.length =
        qOut :: qmid ++ [qIn])
    (hOut : 1 ≤ qOut)
    (hIn : 1 ≤ qIn) :
    2 ^ (n - 1) + 5 * 2 ^ (n - 3)
      ≤
    ∑ v ∈ (Finset.univ.erase deleted : Finset V),
      2 ^
        exponentAfterDeleteAt C
          (by rw [hcard]; omega)
          deleted t v := by
  let hcard3 : 3 ≤ Fintype.card V := by
    rw [hcard]
    omega
  let hother :=
    child_other_nonempty_of_card_ge_three
      hcard3 hir
  have hgain :
      centreExponent (C i) t + 1 ≤
        centreExponent
          ((C i).restrictDelete deleted hir hother) t :=
    centreExponent_gain_delete_of_rotated_positive_ends
      (C i) hir hother pre post hsplit ht0
      qOut qIn qmid hqrot hOut hIn
  exact
    six_point_concrete_minimum_deletion_compensated_of_one_gain
      C hcard hn ht0
      top deleted i
      hdelTop hir hit
      hTop hMin hgain

theorem no_nonTop_positive_positive_ray_of_no_compensated_minimum_deletion
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
    {i deleted : V}
    (hit : i ≠ top)
    (hdelTop : deleted ≠ top)
    (hir : i ≠ deleted)
    (pre post : List (OtherVertex i))
    (hsplit :
      (C i).rays =
        pre ++ deletedParentRay deleted i hir :: post)
    (qOut qIn : ℕ)
    (qmid : List ℕ)
    (hqrot :
      (quotientList t (C i).gaps).rotate pre.length =
        qOut :: qmid ++ [qIn])
    (hOut : 1 ≤ qOut)
    (hIn : 1 ≤ qIn) :
    False := by
  have hcomp :=
    six_point_nonTop_positive_positive_ray_gives_compensated_deletion
      C hcard hn ht0
      top i deleted hit hdelTop hir
      hTop hMin pre post hsplit
      qOut qIn qmid hqrot hOut hIn
  exact (hNoMin deleted hdelTop) hcomp

/-- Convenient hard-branch form: any ray flanked by positive cyclic quotients
at a minimum centre must point to the sharp top. -/
theorem positive_positive_ray_eq_top_of_no_compensated_minimum_deletion
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
    {i deleted : V}
    (hit : i ≠ top)
    (hir : i ≠ deleted)
    (pre post : List (OtherVertex i))
    (hsplit :
      (C i).rays =
        pre ++ deletedParentRay deleted i hir :: post)
    (qOut qIn : ℕ)
    (qmid : List ℕ)
    (hqrot :
      (quotientList t (C i).gaps).rotate pre.length =
        qOut :: qmid ++ [qIn])
    (hOut : 1 ≤ qOut)
    (hIn : 1 ≤ qIn) :
    deleted = top := by
  by_contra hdelTop
  exact no_nonTop_positive_positive_ray_of_no_compensated_minimum_deletion
    C hcard hn ht0 top hTop hMin hNoMin
    hit hdelTop hir
    pre post hsplit qOut qIn qmid hqrot hOut hIn

#print axioms six_point_nonTop_positive_positive_ray_gives_compensated_deletion
#print axioms no_nonTop_positive_positive_ray_of_no_compensated_minimum_deletion
#print axioms positive_positive_ray_eq_top_of_no_compensated_minimum_deletion

end JSP000404Research
