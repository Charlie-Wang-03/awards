import JSP000404Research.SupportThreeMiddleOrDeletionGain
import JSP000404Research.SupportThreeMiddleHiddenTwoHalfCapBridges
import Mathlib.Tactic

/-!
# Actual six-centre geometry: exposure, separated tiny matching, or deletion gain

A support-three n-3 centre pinned at an actual sharp top admits an
unconditional trichotomy:
* it is strictly exposed;
* or it yields two disjoint genuinely tiny (< lambda/2) angular bridges
  whose four cross-cluster angles and four angles to the top are > lambda;
* or deleting some actual non-top original vertex raises its exponent by one.

This is not a Hall matching of sources to true Boolean holes; no global
simultaneous non-reuse claim is made.
-/

namespace JSP000404Research

def TwoSeparatedHalfCapBridges
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (top i : V) (lam : ℝ) : Prop :=
  ∃ r b c d : OtherVertex i,
    r ≠ b ∧ r ≠ c ∧ r ≠ d ∧
    b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    EuclideanGeometry.angle (p r.1) (p i) (p b.1) < lam / 2 ∧
    EuclideanGeometry.angle (p c.1) (p i) (p d.1) < lam / 2 ∧
    lam < EuclideanGeometry.angle (p top) (p i) (p r.1) ∧
    lam < EuclideanGeometry.angle (p top) (p i) (p b.1) ∧
    lam < EuclideanGeometry.angle (p top) (p i) (p c.1) ∧
    lam < EuclideanGeometry.angle (p top) (p i) (p d.1) ∧
    lam < EuclideanGeometry.angle (p r.1) (p i) (p c.1) ∧
    lam < EuclideanGeometry.angle (p r.1) (p i) (p d.1) ∧
    lam < EuclideanGeometry.angle (p b.1) (p i) (p c.1) ∧
    lam < EuclideanGeometry.angle (p b.1) (p i) (p d.1)

theorem six_point_support_three_exposed_or_two_halfcap_bridges_or_actual_gain
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top i : V}
    (hit : i ≠ top)
    (hs : SharpAt p delta lam top)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport : positiveSupport (centreQuotient C t) = 3) :
    StrictlyExposedAt p i ∨
    TwoSeparatedHalfCapBridges (p := p) top i lam ∨
    (∃ deleted : V, ∃ hir : i ≠ deleted,
       deleted ≠ top ∧
       let hother :
           Nonempty (OtherVertex (survivingCentre deleted i hir)) :=
         child_other_nonempty_of_card_ge_three
           (by rw [hcard]; omega) hir
       centreExponent C t + 1 ≤
         centreExponent (C.restrictDelete deleted hir hother) t) := by
  have hsplit :=
    support_three_pinned_middle_or_nonTop_deletion_gain
      hp hcap hcard hn hdelta0 hdeltaHalf
      ht hlam hit.symm hs C hexp hsupport
  rcases hsplit with hmid | hgain
  · by_cases hstrict : StrictlyExposedAt p i
    · exact Or.inl hstrict
    · right
      left
      change TwoSeparatedHalfCapBridges (p := p) top i lam
      exact nonexposed_middle_hidden_two_disjoint_halfcap_bridges
        hp hcap C hcard hn hdelta0 hdeltaHalf ht hlam
        hit hexp hsupport hmid hstrict
  · exact Or.inr (Or.inr hgain)

#print axioms six_point_support_three_exposed_or_two_halfcap_bridges_or_actual_gain

end JSP000404Research
