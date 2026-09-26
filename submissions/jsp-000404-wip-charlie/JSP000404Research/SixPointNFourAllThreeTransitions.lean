import JSP000404Research.SixPointNFourPhaseCover
import JSP000404Research.SixPointNFourEquality
import JSP000404Research.SameSignUnitGapSlot
import JSP000404Research.UnitSameSignOccurrence
import JSP000404Research.SupportThreeTransitionDichotomy
import Mathlib.Tactic

/-!
# A full n=4 unit-slot phase cover forces all five minima to have three transitions

In the ten-slot equality terminal every non-top centre has

  exponent = 1,
  unitSupport = 2,
  positiveSupport = 3.

A support-three centre has either one or three sign transitions.  If it had
only one, the unique-transition two-block decomposition together with the two
unit quotients would force a same-sign unit occurrence.  That occurrence
produces a concrete GlobalUnitGapSlot which is unusable by a transition-only
critical obstruction family.  The n=4 nine-slot phase-cover contradiction then
rules out the one-transition case.

Hence every one of the five minima must use all three positive transition
slots.
-/

namespace JSP000404Research

theorem six_point_n_four_one_transition_minimum_has_sameSign_slot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (i : V)
    (hunit :
      unitSupport (centreQuotient (C i) t) = 2)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = 3)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : (C i).rays = first :: rest)
    (htrans :
      boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) = 1) :
    ∃ u : GlobalUnitGapSlot C t,
      u.1 = i ∧
      GlobalUnitGapSameSign C t u := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by norm_num : 1 ≤ 4) hdelta0 ht
  have htone :
      1 ≤ t :=
    sendov_scale_one_le (by norm_num : 1 ≤ 4) hdelta0 ht
  have hchanges :
      ChangesOnlyOnPositive
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t (C i).gaps) :=
    centre_changesOnlyOnPositive
      hp hcap htpos htone hlam i (C i)
      first rest hrays
  obtain ⟨pre, post, qe, _hqe0, hq, hsign⟩ :=
    one_transition_positive_gap_decomposition
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t (C i).gaps)
      hchanges htrans
  have hunitList :
      listUnitCount (quotientList t (C i).gaps) = 2 := by
    rw [centre_listUnitCount_eq_unitSupport]
    exact hunit
  have hcount :
      listUnitCount (pre ++ qe :: post) = 2 := by
    rw [← hq]
    exact hunitList
  have hsame :
      SameSignQuotientOccurs 1
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t (C i).gaps) := by
    rw [hq, hsign]
    exact sameSign_unit_occurs_of_two_units_two_blocks
      (raySignAt hp i first) pre post qe hcount
  exact exists_globalUnitGap_sameSign_of_occurs
    C t i first rest hrays hsame

/-- Under a full transition-only unit-gap cover, every non-top centre in the
n=4 equality terminal has exactly three sign transitions. -/
theorem six_point_n_four_cover_forces_all_minima_three_transitions
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
        (4 : ℝ) + delta ≤ (T.card : ℝ) * delta)
    (hcover : PredicateCovers A S) :
    ∀ i : V, i ≠ top →
      ∃ first : OtherVertex i,
        ∃ rest : List (OtherVertex i),
          (C i).rays = first :: rest ∧
          boolTransitionCountFrom
            (raySignAt hp i first)
            (liftedCentreSignPath hp i first rest) = 3 := by
  have hshape :=
    six_point_n_four_unit_budget_equality_forces_11200
      C hdelta0 hdeltaHalf ht hcard
      top hTop hMin hunitTotal
  have htpos :
      0 < t :=
    sendov_scale_pos (by norm_num : 1 ≤ 4) hdelta0 ht
  have htone :
      1 ≤ t :=
    sendov_scale_one_le (by norm_num : 1 ≤ 4) hdelta0 ht
  intro i hitop
  have hiShape := hshape i hitop
  have hunit : unitSupport (centreQuotient (C i) t) = 2 :=
    hiShape.1
  have hsupport :
      positiveSupport (centreQuotient (C i) t) = 3 :=
    hiShape.2.1
  obtain ⟨first, rest, hrays, hcase⟩ :=
    support_three_transition_count_one_or_three
      hp hcap htpos htone hlam
      i (C i) hsupport
  rcases hcase with hOne | hThree
  · obtain ⟨u, _hui, husame⟩ :=
      six_point_n_four_one_transition_minimum_has_sameSign_slot
        hp hcap hdelta0 ht hlam C i
        hunit hsupport first rest hrays hOne
    have hno :=
      no_six_point_n_four_globalUnitGapSlot_cover_of_unusable
        C hdelta0 hdeltaHalf ht hcard
        top hTop hMin A S u
        (hSameUnusable u husame)
        hcoverLower
    exact False.elim (hno hcover)
  · exact ⟨first, rest, hrays, hThree⟩

#print axioms six_point_n_four_one_transition_minimum_has_sameSign_slot
#print axioms six_point_n_four_cover_forces_all_minima_three_transitions

end JSP000404Research
