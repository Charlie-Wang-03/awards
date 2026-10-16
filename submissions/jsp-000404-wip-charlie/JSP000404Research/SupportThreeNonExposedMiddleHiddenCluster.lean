import JSP000404Research.SupportThreeMiddleHiddenClusterGeometry
import JSP000404Research.SupportThreeTransitionDichotomy
import Mathlib.Tactic

/-!
# Non-exposed middle-hidden support three: unconditional transition removal

The certified support-three transition dichotomy forces exactly three
transitions for a non-strictly-exposed centre. Combining this with the
pinned middle-hidden geometric certificate eliminates the independent
three-transition witness from the geometric hypotheses.

All eight inter-cluster ray angles exceed lambda; the two remaining
intra-cluster angles have combined mass at most delta*lambda.

This is an AngleCap-derived local geometric constraint, NOT a proof
that the global dyadic profile debt can be matched into true holes.
-/

namespace JSP000404Research

theorem nonexposed_support_three_middle_hidden_cluster_angles_gt_lam
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    {top i : V}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hit : i ≠ top)
    (hexp : centreExponent C t = n - 3)
    (hsupport : positiveSupport (centreQuotient C t) = 3)
    (hmiddle : SupportThreePinnedMiddleShape (t := t) hp
      (Ne.symm hit) C)
    (hnot : ¬ StrictlyExposedAt p i) :
    ∃ r b c d : OtherVertex i,
      r.1 ≠ top ∧ b.1 ≠ top ∧ c.1 ≠ top ∧ d.1 ≠ top ∧
      r ≠ b ∧ r ≠ c ∧ r ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      EuclideanGeometry.angle (p r.1) (p i) (p b.1) +
        EuclideanGeometry.angle (p c.1) (p i) (p d.1) ≤
          delta * lam ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p r.1) ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p b.1) ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p c.1) ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p d.1) ∧
      lam < EuclideanGeometry.angle (p r.1) (p i) (p c.1) ∧
      lam < EuclideanGeometry.angle (p r.1) (p i) (p d.1) ∧
      lam < EuclideanGeometry.angle (p b.1) (p i) (p c.1) ∧
      lam < EuclideanGeometry.angle (p b.1) (p i) (p d.1) := by
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have htone : 1 ≤ t := by
    rw [ht]
    have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hthree :=
    three_transitions_of_support_three_not_strictlyExposed
      hp hcap htpos htone hlam i C hsupport hnot
  exact support_three_middle_hidden_all_cross_cluster_angles_gt_lam
    hp hcap C hcard hn hdelta0 hdeltaHalf ht hlam
    hit hexp hsupport hmiddle hthree

#print axioms nonexposed_support_three_middle_hidden_cluster_angles_gt_lam

end JSP000404Research
