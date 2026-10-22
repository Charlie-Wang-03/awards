import JSP000404Research.SixPointNFourAllThreeTransitions
import JSP000404Research.FarthestStrictExposure
import JSP000404Research.SameSignUnitGapSlot
import Mathlib.Tactic

/-!
# Unconditional same-sign original-centre unit slot in the n=4 equality terminal

In the six-original-point n=4 profile, assume one top exponent-three centre
and five exponent-one minima, with the ten unit-gap slots at equality.

Choose a strictly exposed centre other than the top by the farthest-point
lemma.  This original centre is therefore a minimum, and the ten-slot
arithmetic equality gives exactly two unit quotients at that centre.
Strict exposure supplies a one-transition sign path.  Two unit quotients
on such a path force one same-sign unit occurrence on an actual indexed
original-centre gap.

Consequently no more than nine of the ten true unit-gap *locations* can fail
to be certified same-sign. This does NOT identify gap locations with Boolean
true holes, nor prove a global non-reusing six-source payment.
-/

namespace JSP000404Research

open scoped BigOperators

/-- No exact-angle witness or choice of witness sign branch is required:
ten-slot equality itself produces an actual same-sign original-centre gap. -/
theorem six_point_n_four_equality_exists_global_sameSign_unit_slot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = 1)
    (hunitTotal :
      (∑ i : V, unitSupport (centreQuotient (C i) t)) = 10) :
    ∃ u : GlobalUnitGapSlot C t,
      GlobalUnitGapSameSign C t u := by
  obtain ⟨j, hjTop, hExpose⟩ :=
    exists_strictlyExposed_ne_fixed
      hp (by rw [hcard]; norm_num) top
  have hshape :=
    six_point_n_four_unit_budget_equality_forces_11200
      C hdelta0 hdeltaHalf ht hcard
      top hTop hMin hunitTotal
  have hjShape := hshape j hjTop
  obtain ⟨first, rest, hrays, hOne⟩ :=
    one_sign_transition_of_strictlyExposed
      hp (C j) hExpose
  obtain ⟨u, _hcentre, hsame⟩ :=
    six_point_n_four_one_transition_minimum_has_sameSign_slot
      hp hcap hdelta0 ht hlam C j
      hjShape.1 hjShape.2.1
      first rest hrays hOne
  exact ⟨u, hsame⟩

/-- At equality there are at most nine unit-gap locations that are not
certified same-sign, with no exact-angle-witness hypothesis. -/
theorem six_point_n_four_equality_nonSameSign_slot_card_le_nine
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = 1)
    (hunitTotal :
      (∑ i : V, unitSupport (centreQuotient (C i) t)) = 10) :
    ((Finset.univ : Finset (GlobalUnitGapSlot C t)).filter
      (fun u => ¬ GlobalUnitGapSameSign C t u)).card ≤ 9 := by
  classical
  obtain ⟨u, hu⟩ :=
    six_point_n_four_equality_exists_global_sameSign_unit_slot
      hp hcap hdelta0 hdeltaHalf ht hlam
      C hcard top hTop hMin hunitTotal
  let S : Finset (GlobalUnitGapSlot C t) :=
    Finset.univ.filter (fun v => ¬ GlobalUnitGapSameSign C t v)
  have hsubset : S ⊆ Finset.univ.erase u := by
    intro v hv
    have hvNot : ¬ GlobalUnitGapSameSign C t v :=
      (Finset.mem_filter.mp hv).2
    have hvne : v ≠ u := by
      intro heq
      subst v
      exact hvNot hu
    exact Finset.mem_erase.mpr ⟨hvne, Finset.mem_univ v⟩
  have hcardTen : Fintype.card (GlobalUnitGapSlot C t) = 10 :=
    (globalUnitGapSlot_card_eq_sum_unitSupport C t).trans hunitTotal
  have herase : (Finset.univ.erase u).card = 9 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ u),
      Finset.card_univ, hcardTen]
    norm_num
  change S.card ≤ 9
  exact (Finset.card_le_card hsubset).trans_eq herase

#print axioms six_point_n_four_equality_exists_global_sameSign_unit_slot
#print axioms six_point_n_four_equality_nonSameSign_slot_card_le_nine

end JSP000404Research
