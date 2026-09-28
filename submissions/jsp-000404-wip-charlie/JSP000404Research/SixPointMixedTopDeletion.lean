import JSP000404Research.SixPointTopDeletionWeight
import JSP000404Research.SixPointConcreteTopDeletion
import JSP000404Research.CyclicPositiveRayDeletionGain
import JSP000404Research.SixPointSupportTwoDeletionReduction
import Mathlib.Tactic

/-!
# Four arbitrary top-deletion gains compensate the sharp top

The top-deletion weight ledger only needs four surviving minima to gain one
exponent unit; it does not matter why they gain.

Support-three minima always gain when the sharp top is deleted.  A support-two
minimum also gains if the ray to the top is flanked by positive cyclic
quotients.

This file packages the mixed gain ledger.  In a hard branch with no
compensated top deletion, at most three minima can belong to the union

  {support-three minima}
    union
  {support-two minima whose top ray is positive-positive pinned}.

Hence every mixed low-support profile contains a genuinely separated
support-two centre; in a profile with no support-one minimum there are at
least two such separated support-two centres.
-/

namespace JSP000404Research

open scoped BigOperators

def SixPointNoCompensatedTopDeletion
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard3 : 3 ≤ Fintype.card V)
    (top : V)
    (t : ℝ)
    (n : ℕ) : Prop :=
  ¬ (
    2 ^ (n - 1) + 5 * 2 ^ (n - 3)
      ≤
    ∑ v ∈ (Finset.univ.erase top : Finset V),
      2 ^ exponentAfterDeleteTopAt C hcard3 top t v
  )

theorem six_point_top_deletion_compensated_of_four_concrete_gains
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 3 ≤ n)
    (ht0 : 0 ≤ t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (good : Finset V)
    (hgoodSub :
      good ⊆ (Finset.univ.erase top : Finset V))
    (hgoodCard : good.card = 4)
    (hgain :
      ∀ v ∈ good,
        centreExponent (C v) t + 1 ≤
          exponentAfterDeleteTopAt C
            (by rw [hcard]; omega)
            top t v) :
    2 ^ (n - 1) + 5 * 2 ^ (n - 3)
      ≤
    ∑ v ∈ (Finset.univ.erase top : Finset V),
      2 ^ exponentAfterDeleteTopAt C
        (by rw [hcard]; omega) top t v := by
  apply five_survivor_weight_ge_six_point_profile_of_four_gains
      hn top hcard
      (exponentAfterDeleteTopAt C
        (by rw [hcard]; omega) top t)
      good hgoodSub hgoodCard
  · intro v hvt
    rw [← hMin v hvt]
    exact exponent_le_after_delete_top
      C top ht0 (by rw [hcard]; omega) hvt
  · intro v hv
    have hvt : v ≠ top := by
      have hvS := hgoodSub hv
      simpa using (Finset.mem_erase.mp hvS).1
    have hg := hgain v hv
    rw [hMin v hvt] at hg
    omega

/-- A positive-positive pin at the top ray is a top-deletion gain, regardless
of the support count of the centre. -/
theorem exponent_add_one_le_after_delete_top_of_positive_positive_pin
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard3 : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht0 : 0 ≤ t)
    {top i : V}
    (hit : i ≠ top)
    (pre post : List (OtherVertex i))
    (hsplit :
      (C i).rays =
        pre ++ deletedParentRay top i hit :: post)
    (qOut qIn : ℕ)
    (qmid : List ℕ)
    (hqrot :
      (quotientList t (C i).gaps).rotate pre.length =
        qOut :: qmid ++ [qIn])
    (hOut : 1 ≤ qOut)
    (hIn : 1 ≤ qIn) :
    centreExponent (C i) t + 1 ≤
      exponentAfterDeleteTopAt C hcard3 top t i := by
  unfold exponentAfterDeleteTopAt
  rw [dif_pos hit]
  dsimp only
  let hother :=
    child_other_nonempty_of_card_ge_three
      hcard3 hit
  exact centreExponent_gain_delete_of_rotated_positive_ends
    (C i) hit hother
    pre post hsplit ht0
    qOut qIn qmid hqrot hOut hIn

/-- If four minima have any certified top-deletion gains, a hard top-deletion
branch is impossible. -/
theorem no_four_top_deletion_gains
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 3 ≤ n)
    (ht0 : 0 ≤ t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n)
    (good : Finset V)
    (hgoodSub :
      good ⊆ (Finset.univ.erase top : Finset V))
    (hgoodCard : good.card = 4)
    (hgain :
      ∀ v ∈ good,
        centreExponent (C v) t + 1 ≤
          exponentAfterDeleteTopAt C
            (by rw [hcard]; omega)
            top t v) :
    False := by
  exact hNoTop
    (six_point_top_deletion_compensated_of_four_concrete_gains
      C hcard hn ht0 top hTop hMin
      good hgoodSub hgoodCard hgain)

#print axioms SixPointNoCompensatedTopDeletion
#print axioms six_point_top_deletion_compensated_of_four_concrete_gains
#print axioms exponent_add_one_le_after_delete_top_of_positive_positive_pin
#print axioms no_four_top_deletion_gains

end JSP000404Research
