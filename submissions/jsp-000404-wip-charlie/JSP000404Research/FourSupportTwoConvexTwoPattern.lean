import JSP000404Research.FourSupportTwoCrossingCore
import JSP000404Research.FourPointRadonPairing
import JSP000404Research.StrictExposureConvexHull
import JSP000404Research.SupportLeTwoTransitionInterval
import Mathlib.Tactic

/-!
# Convex-position reduction from three support-two matchings to two

The sine-product terminal leaves three double-transposition patterns.
For four convexly exposed points, Radon supplies one crossing pairing.
The pattern corresponding to that crossing pairing is impossible by the
crossing-diagonal angle-sum obstruction.

Hence every concrete four-point support-two terminal has only two surviving
patterns once its actual crossing pairing is known.

The second theorem derives the required convex-position exclusions directly
from four support<=2 centre certificates.
-/

namespace JSP000404Research

private def SupportTwoPattern1
    {V : Type*} (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p b) (p d) (p c) ≤ delta * lam

private def SupportTwoPattern2
    {V : Type*} (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam ∧
  EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p d) (p c) ≤ delta * lam

private def SupportTwoPattern3
    {V : Type*} (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p d) (p b) ≤ delta * lam

theorem four_supportTwo_pattern3_reduce_to_two_of_convex_position
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (hlamHalf : lam ≤ Real.pi / 2)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha :
      p a ∉ convexHull ℝ ({p b,p c,p d} : Set Plane))
    (hb :
      p b ∉ convexHull ℝ ({p a,p c,p d} : Set Plane))
    (hc :
      p c ∉ convexHull ℝ ({p a,p b,p d} : Set Plane))
    (hd :
      p d ∉ convexHull ℝ ({p a,p b,p c} : Set Plane))
    (hpat : FourSupportTwoDerangementPattern3 p delta lam a b c d) :
    (
      (segment ℝ (p a) (p b) ∩ segment ℝ (p c) (p d)).Nonempty ∧
      (SupportTwoPattern1 p delta lam a b c d ∨
       SupportTwoPattern2 p delta lam a b c d)
    )
    ∨
    (
      (segment ℝ (p a) (p c) ∩ segment ℝ (p b) (p d)).Nonempty ∧
      (SupportTwoPattern1 p delta lam a b c d ∨
       SupportTwoPattern3 p delta lam a b c d)
    )
    ∨
    (
      (segment ℝ (p a) (p d) ∩ segment ℝ (p b) (p c)).Nonempty ∧
      (SupportTwoPattern2 p delta lam a b c d ∨
       SupportTwoPattern3 p delta lam a b c d)
    ) := by
  have hcross :=
    four_convex_position_has_crossing_pairing
      (hp.ne hab) (hp.ne hac) (hp.ne had)
      (hp.ne hbc) (hp.ne hbd) (hp.ne hcd)
      ha hb hc hd
  unfold FourSupportTwoDerangementPattern3 at hpat
  unfold FourSupportTwoAnglePattern3Core at hpat
  rcases hcross with hABCD | hACBD | hADBC
  · left
    refine ⟨hABCD, ?_⟩
    rcases hpat with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exact False.elim
        (four_supportTwo_pattern3_impossible_of_cross_ab_cd
          hp hdeltaHalf hlampos hlamHalf
          hab hac had hbc hbd hcd
          ha hb hABCD h3)
  · right; left
    refine ⟨hACBD, ?_⟩
    rcases hpat with h1 | h2 | h3
    · exact Or.inl h1
    · exact False.elim
        (four_supportTwo_pattern2_impossible_of_cross_ac_bd
          hp hdeltaHalf hlampos hlamHalf
          hab hac had hbc hbd hcd
          ha hc hACBD h2)
    · exact Or.inr h3
  · right; right
    refine ⟨hADBC, ?_⟩
    rcases hpat with h1 | h2 | h3
    · exact False.elim
        (four_supportTwo_pattern1_impossible_of_cross_ad_bc
          hp hdeltaHalf hlampos hlamHalf
          hab hac had hbc hbd hcd
          ha hd hADBC h1)
    · exact Or.inl h2
    · exact Or.inr h3

/-- Four support<=2 concrete centres reduce the three-pattern terminal to two,
with the surviving pair indexed by the actual crossing pairing. -/
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
      (SupportTwoPattern1 p delta lam a b c d ∨
       SupportTwoPattern2 p delta lam a b c d)
    )
    ∨
    (
      (segment ℝ (p a) (p c) ∩ segment ℝ (p b) (p d)).Nonempty ∧
      (SupportTwoPattern1 p delta lam a b c d ∨
       SupportTwoPattern3 p delta lam a b c d)
    )
    ∨
    (
      (segment ℝ (p a) (p d) ∩ segment ℝ (p b) (p c)).Nonempty ∧
      (SupportTwoPattern2 p delta lam a b c d ∨
       SupportTwoPattern3 p delta lam a b c d)
    ) := by
  have hn1 : 1 ≤ n := by omega
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have htone : (1 : ℝ) ≤ t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
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

#print axioms four_supportTwo_pattern3_reduce_to_two_of_convex_position
#print axioms four_supportLeTwo_secondLayer_reduce_to_two

end JSP000404Research
