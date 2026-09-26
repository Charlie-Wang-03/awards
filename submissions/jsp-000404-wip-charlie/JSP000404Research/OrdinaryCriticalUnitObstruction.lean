import JSP000404Research.TransitionSameSignDisjoint
import JSP000404Research.SixPointUnitPhaseCoverAllN
import JSP000404Research.CriticalPhaseInterval
import Mathlib.Tactic

/-!
# Ordinary critical unit-gap obstruction predicate

A concrete ordinary critical obstruction consists of a GlobalUnitGapSlot u
whose q=1 coordinate is an actual adjacent sign transition.  If that adjacent
gap begins at normalized projective direction alpha and has normalized width
s, then

  1 <= s <= 1+delta

and its bad-phase interval is

  [alpha+s-1, alpha+delta].

The slot predicate below stores exactly this concrete data.

Because the slot is required to be an ordinary sign transition,
TransitionSameSignDisjoint immediately shows that a same-sign unit slot can
never carry such an obstruction.  Hence the unified six-point no-cover theorem
applies without any extra geometric unusability assumption.
-/

namespace JSP000404Research

/-- Normalized projective theta of a concrete ray. -/
noncomputable def normalizedRayThetaAt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t : ℝ)
    (i : V)
    (j : OtherVertex i) : ℝ :=
  t * (rayThetaAt hp i j / Real.pi)

/-- Concrete ordinary critical-unit obstruction attached to one global q=1
slot. -/
def OrdinaryCriticalUnitBadAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t delta : ℝ)
    (u : GlobalUnitGapSlot C t)
    (x : ℝ) : Prop :=
  ∃ m : ℕ, ∃ hm : m + 1 < (C u.1).rays.length,
    u.2.1.val = m ∧
    raySignAt hp u.1
        ((C u.1).rays.get ⟨m, by omega⟩) ≠
      raySignAt hp u.1
        ((C u.1).rays.get ⟨m + 1, hm⟩) ∧
    let alpha :=
      normalizedRayThetaAt hp t u.1
        ((C u.1).rays.get ⟨m, by omega⟩)
    let s :=
      t * ((rayThetaAt hp u.1
          ((C u.1).rays.get ⟨m + 1, hm⟩) -
        rayThetaAt hp u.1
          ((C u.1).rays.get ⟨m, by omega⟩)) / Real.pi)
    1 ≤ s ∧
    s ≤ 1 + delta ∧
    criticalBadLeft alpha s ≤ x ∧
    x ≤ criticalBadRight alpha delta

/-- Every concrete ordinary critical obstruction is carried by an ordinary
transition slot. -/
theorem ordinaryCriticalUnitBadAt_implies_transition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t delta : ℝ)
    (u : GlobalUnitGapSlot C t)
    {x : ℝ}
    (hbad : OrdinaryCriticalUnitBadAt C t delta u x) :
    GlobalUnitGapOrdinaryTransition C t u := by
  rcases hbad with
    ⟨m, hm, hidx, hsign, _hs1, _hsTop, _hxL, _hxR⟩
  refine ⟨m, hm, hidx, ?_, hsign⟩
  exact u.2.2

/-- Same-sign unit slots are automatically unusable by the ordinary critical
obstruction family. -/
theorem ordinaryCriticalUnitBadAt_not_of_sameSign
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t delta : ℝ)
    (u : GlobalUnitGapSlot C t)
    (hsame : GlobalUnitGapSameSign C t u) :
    ∀ x : ℝ, ¬ OrdinaryCriticalUnitBadAt C t delta u x := by
  intro x hbad
  exact
    (globalUnitGapSameSign_not_ordinaryTransition
      C t u hsame)
      (ordinaryCriticalUnitBadAt_implies_transition
        C t delta u hbad)

/-- Unified six-point terminal for the actual ordinary critical-unit
obstruction family. -/
theorem no_six_point_ordinaryCriticalUnit_cover
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3)
    (S : Finset (GlobalUnitGapSlot C t))
    (hcoverLower :
      ∀ T : Finset (GlobalUnitGapSlot C t), T ⊆ S →
        PredicateCovers
          (OrdinaryCriticalUnitBadAt C t delta) T →
        (n : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers
      (OrdinaryCriticalUnitBadAt C t delta) S := by
  exact
    no_six_point_transition_only_globalUnitGapSlot_cover
      hcap hn hdelta0 hdeltaHalf ht hlam
      C hcard top hTop hMin
      (OrdinaryCriticalUnitBadAt C t delta)
      S
      (fun u hsame =>
        ordinaryCriticalUnitBadAt_not_of_sameSign
          C t delta u hsame)
      hcoverLower

#print axioms ordinaryCriticalUnitBadAt_implies_transition
#print axioms ordinaryCriticalUnitBadAt_not_of_sameSign
#print axioms no_six_point_ordinaryCriticalUnit_cover

end JSP000404Research
