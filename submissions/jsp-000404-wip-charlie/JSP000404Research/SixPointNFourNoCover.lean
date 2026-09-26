import JSP000404Research.SixPointNFourAllThreeTransitions
import JSP000404Research.FarthestStrictExposure
import JSP000404Research.ExposedSupportIntervalGeneral
import Mathlib.Tactic

/-!
# No full transition-only unit-slot phase cover in the n=4 six-point terminal

The ten-slot equality terminal has one top centre and five minima.

Assume a full phase cover by critical unit-gap obstructions, with the natural
geometric condition that a same-sign unit gap cannot generate such a
transition obstruction.

The previous module forces every minimum to have exactly three sign
transitions.  On the other hand, relative to the top centre there is always a
different strictly exposed vertex: choose a farthest non-top point.  Since all
non-top vertices are minima, that same centre has three transitions.

But ExposedSupportIntervalGeneral proves that every strictly exposed centre has
exactly one sign transition in its fixed sorted ray cycle.  The two displayed
head/tail decompositions are decompositions of the same nonempty list C.rays,
hence have identical head and tail.  This gives 1=3, contradiction.

Thus the n=4 six-point equality terminal admits no such full phase cover.
-/

namespace JSP000404Research

theorem no_six_point_n_four_transition_only_unit_slot_cover
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = 1)
    (hunitTotal :
      (∑ i : V,
        unitSupport (centreQuotient (C i) t)) = 10)
    (A : GlobalUnitGapSlot C t → ℝ → Prop)
    (S : Finset (GlobalUnitGapSlot C t))
    (hSameUnusable :
      ∀ u : GlobalUnitGapSlot C t,
        GlobalUnitGapSameSign C t u →
        ∀ x : ℝ, ¬ A u x)
    (hcoverLower :
      ∀ T : Finset (GlobalUnitGapSlot C t), T ⊆ S →
        PredicateCovers A T →
        (4 : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers A S := by
  intro hcover
  have hAllThree :=
    six_point_n_four_cover_forces_all_minima_three_transitions
      hp hcap hdelta0 hdeltaHalf ht hlam
      C hcard top hTop hMin hunitTotal
      A S hSameUnusable hcoverLower hcover
  obtain ⟨j, hjTop, hExpose⟩ :=
    exists_strictlyExposed_ne_fixed
      hp (by rw [hcard]; norm_num) top
  obtain ⟨first3, rest3, hrays3, hthree⟩ :=
    hAllThree j hjTop
  obtain ⟨first1, rest1, hrays1, hone⟩ :=
    one_sign_transition_of_strictlyExposed
      hp (C j) hExpose
  have hcons :
      first1 :: rest1 = first3 :: rest3 := by
    rw [← hrays1, ← hrays3]
  have hhead : first1 = first3 :=
    (List.cons.inj hcons).1
  have htail : rest1 = rest3 :=
    (List.cons.inj hcons).2
  subst first3
  subst rest3
  omega

#print axioms no_six_point_n_four_transition_only_unit_slot_cover

end JSP000404Research
