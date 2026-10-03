import JSP000404Research.FourSupportTwoConvexTwoPattern
import JSP000404Research.StrictExposureConvexHull
import JSP000404Research.SupportLeTwoTransitionInterval
import Mathlib.Tactic

/-!
# Support<=2 centres feed the convex three-to-two terminal

This bridge contains the support-specific input omitted from the pure convex
module.  Each support<=2 centre is strictly exposed; four strict exposures
exclude every vertex from the convex hull of the other three.  The pure
convex module then reduces the three double-transposition patterns to two,
indexed by the actual crossing pairing.
-/

namespace JSP000404Research

theorem four_supportLeTwo_secondLayer_reduce_to_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (haSupport : positiveSupport (centreQuotient (C a) t) ≤ 2)
    (hbSupport : positiveSupport (centreQuotient (C b) t) ≤ 2)
    (hcSupport : positiveSupport (centreQuotient (C c) t) ≤ 2)
    (hdSupport : positiveSupport (centreQuotient (C d) t) ≤ 2)
    (hpat : FourSupportTwoDerangementPattern3 p delta lam a b c d) :
    (
      (segment ℝ (p a) (p b) ∩ segment ℝ (p c) (p d)).Nonempty ∧
      (FourSupportTwoMatchingPattern1 p delta lam a b c d ∨
       FourSupportTwoMatchingPattern2 p delta lam a b c d)
    )
    ∨
    (
      (segment ℝ (p a) (p c) ∩ segment ℝ (p b) (p d)).Nonempty ∧
      (FourSupportTwoMatchingPattern1 p delta lam a b c d ∨
       FourSupportTwoMatchingPattern3 p delta lam a b c d)
    )
    ∨
    (
      (segment ℝ (p a) (p d) ∩ segment ℝ (p b) (p c)).Nonempty ∧
      (FourSupportTwoMatchingPattern2 p delta lam a b c d ∨
       FourSupportTwoMatchingPattern3 p delta lam a b c d)
    ) := by
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by
      exact_mod_cast hn3
    linarith
  have htone : (1 : ℝ) ≤ t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by
      exact_mod_cast hn3
    linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hlamHalf : lam ≤ Real.pi / 2 := by
    rw [hlam]
    rw [div_le_iff₀ htpos]
    nlinarith [Real.pi_pos]

  have haExp :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap htpos htone hlam a (C a) haSupport
  have hbExp :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap htpos htone hlam b (C b) hbSupport
  have hcExp :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap htpos htone hlam c (C c) hcSupport
  have hdExp :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap htpos htone hlam d (C d) hdSupport

  obtain ⟨haHull,hbHull,hcHull,hdHull⟩ :=
    four_strictlyExposed_convexHull_exclusions
      hab hac had hbc hbd hcd
      haExp hbExp hcExp hdExp

  exact four_supportTwo_pattern3_reduce_to_two_of_convex_position
    hp hdeltaHalf hlampos hlamHalf
    hab hac had hbc hbd hcd
    haHull hbHull hcHull hdHull hpat

#print axioms four_supportLeTwo_secondLayer_reduce_to_two

end JSP000404Research
