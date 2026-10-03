import JSP000404Research.FourSupportTwoCrossingCore
import JSP000404Research.FourPointRadonPairing
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

def FourSupportTwoMatchingPattern1
    {V : Type*} (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p b) (p d) (p c) ≤ delta * lam

def FourSupportTwoMatchingPattern2
    {V : Type*} (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam ∧
  EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p d) (p c) ≤ delta * lam

def FourSupportTwoMatchingPattern3
    {V : Type*} (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p d) (p b) ≤ delta * lam

def FourSupportTwoCrossingTwoPatternTerminal
    {V : Type*} (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
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
  )

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
    FourSupportTwoCrossingTwoPatternTerminal
      p delta lam a b c d := by
  unfold FourSupportTwoCrossingTwoPatternTerminal
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

#print axioms four_supportTwo_pattern3_reduce_to_two_of_convex_position

end JSP000404Research
