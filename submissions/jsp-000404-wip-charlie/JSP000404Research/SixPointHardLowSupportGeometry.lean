import JSP000404Research.SixPointTwoNonGainers
import JSP000404Research.SeparatedSupportTwoSmallPair
import JSP000404Research.SixPointMixedSupportTransitionBudget
import Mathlib.Tactic

/-!
# Concrete low-support geometry in the hard six-point branch

After excluding compensated top deletion, retain two distinct non-gaining
minima.

* Pure branch: both are separated support-two centres.  Each has a genuine
  delta*lambda-small angle between two non-top rays.

* Mixed branch: one is support one and the other is separated support two.
  The support-two centre has the same non-top small pair.  In addition, global
  transition packing against the sharp top and the support-one centre forces
  its distinguished transition quotient to be at most two.

This is a direct geometric terminal for the remaining compensated-deletion
hard branch.
-/

namespace JSP000404Research

structure SmallPairAwayFromTop
    {V : Type*} {p : V → Plane}
    (top i : V) (delta lam : ℝ) where
  x : OtherVertex i
  y : OtherVertex i
  x_ne_y : x ≠ y
  x_ne_top : x.1 ≠ top
  y_ne_top : y.1 ≠ top
  small :
    EuclideanGeometry.angle (p x.1) (p i) (p y.1)
      ≤ delta * lam

theorem separated_support_two_smallPairWitness
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    {i : V}
    (hit : i ≠ top)
    (hI : centreExponent (C i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = 2)
    (hsep :
      ¬ TopPinnedPositivePair C top i hit t) :
    Nonempty (SmallPairAwayFromTop (p := p) top i delta lam) := by
  obtain ⟨x,y,hxy,hxt,hyt,hsmall⟩ :=
    separated_support_two_has_small_pair_away_from_top
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top hTop hit hI hsupport hsep
  exact ⟨{
    x := x
    y := y
    x_ne_y := hxy
    x_ne_top := hxt
    y_ne_top := hyt
    small := hsmall
  }⟩

/-- Hard branch reduced to two explicit low-support geometric terminals. -/
theorem six_point_hard_lowSupport_geometry
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    (
      ∃ a b : V,
        a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
        positiveSupport (centreQuotient (C a) t) = 2 ∧
        positiveSupport (centreQuotient (C b) t) = 2 ∧
        Nonempty (SmallPairAwayFromTop (p := p) top a delta lam) ∧
        Nonempty (SmallPairAwayFromTop (p := p) top b delta lam)
    )
    ∨
    (
      ∃ a b : V,
        a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
        positiveSupport (centreQuotient (C a) t) = 1 ∧
        positiveSupport (centreQuotient (C b) t) = 2 ∧
        Nonempty (SmallPairAwayFromTop (p := p) top b delta lam) ∧
        ∃ HB : HighExponentTransitionIntervalCertificate hp t b (C b),
          HB.qe ≤ 2
    ) := by
  rcases two_nonGaining_lowSupport_witnesses
      hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
      top hTop hMin hNoTop
    with hpure | hmixed
  · obtain ⟨a,b,hat,hbt,hab,_haNG,_hbNG,
      hsupA,hsupB,hsepA,hsepB⟩ := hpure
    left
    refine ⟨a,b,hat,hbt,hab,hsupA,hsupB,?_,?_⟩
    · exact separated_support_two_smallPairWitness
        hp hcap C hcard hn5 hdelta0 hdeltaHalf
        ht hlam top hTop hat (hMin a hat) hsupA hsepA
    · exact separated_support_two_smallPairWitness
        hp hcap C hcard hn5 hdelta0 hdeltaHalf
        ht hlam top hTop hbt (hMin b hbt) hsupB hsepB
  · obtain ⟨a,b,hat,hbt,hab,_haNG,_hbNG,
      hsupA,hsupB,hsepB⟩ := hmixed
    right
    refine ⟨a,b,hat,hbt,hab,hsupA,hsupB,?_,?_⟩
    · exact separated_support_two_smallPairWitness
        hp hcap C hcard hn5 hdelta0 hdeltaHalf
        ht hlam top hTop hbt (hMin b hbt) hsupB hsepB
    · exact mixed_support_one_one_support_two_transition_le_two
        hp hcap (by omega : 4 ≤ n)
        hdelta0 hdeltaHalf ht hlam
        hat.symm hbt.symm hab
        (C top) (C a) (C b)
        hTop (hMin a hat) hsupA
        (by rw [hsupB]; omega)

#print axioms separated_support_two_smallPairWitness
#print axioms six_point_hard_lowSupport_geometry

end JSP000404Research
