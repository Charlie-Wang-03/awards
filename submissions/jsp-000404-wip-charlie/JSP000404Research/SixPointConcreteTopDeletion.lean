import JSP000404Research.SixPointTopDeletionWeight
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

/-!
# Concrete compensated deletion of the sharp top with four support-three minima

This is the geometric realization of SixPointTopDeletionWeight.

For every parent vertex v different from top, define the exponent of its
surviving centre after deleting top using CentreProjectiveCycle.restrictDelete.

In the six-point terminal:

* every minimum has parent exponent n-3;
* deletion never decreases a surviving exponent;
* if a minimum has quotient support three, deletion of the sharp top raises
  its exponent by at least one.

Therefore any four support-three minima compensate the complete dyadic weight
of the deleted n-1 top centre.
-/

namespace JSP000404Research

noncomputable def exponentAfterDeleteTopAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard3 : 3 ≤ Fintype.card V)
    (top : V)
    (t : ℝ)
    (v : V) : ℕ :=
  if h : v ≠ top then
    let hother :=
      child_other_nonempty_of_card_ge_three
        hcard3 h
    centreExponent
      ((C v).restrictDelete top h hother) t
  else 0

theorem exponent_le_after_delete_top
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (top : V)
    {t : ℝ}
    (ht0 : 0 ≤ t)
    (hcard3 : 3 ≤ Fintype.card V)
    {v : V}
    (hvt : v ≠ top) :
    centreExponent (C v) t ≤
      exponentAfterDeleteTopAt C hcard3 top t v := by
  unfold exponentAfterDeleteTopAt
  rw [dif_pos hvt]
  dsimp only
  let hother :=
    child_other_nonempty_of_card_ge_three
      hcard3 hvt
  exact centreExponent_mono_restrictDelete
    (C v) hvt hother ht0

theorem exponent_add_one_le_after_delete_top_of_support_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hcard3 : 3 ≤ Fintype.card V)
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    {v : V}
    (hvt : v ≠ top)
    (hV : centreExponent (C v) t = n - 3)
    (hsupV :
      positiveSupport (centreQuotient (C v) t) = 3) :
    centreExponent (C v) t + 1 ≤
      exponentAfterDeleteTopAt C hcard3 top t v := by
  have hdelta1 : delta < 1 := by linarith
  have hsharp :
      SharpAt p delta lam top :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      top (C top) hTop
  unfold exponentAfterDeleteTopAt
  rw [dif_pos hvt]
  dsimp only
  let hother :=
    child_other_nonempty_of_card_ge_three
      hcard3 hvt
  exact sharp_support_three_delete_sharp_gain
    hp hcap hcard3 hn4 hdelta0 hdeltaHalf
    ht hlam hvt.symm hsharp (C v) hV hsupV

/-- Concrete six-point compensated top deletion once four minima are known to
have support three. -/
theorem six_point_top_deletion_compensated_of_four_support_three
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (good : Finset V)
    (hgoodSub :
      good ⊆ (Finset.univ.erase top : Finset V))
    (hgoodCard : good.card = 4)
    (hgoodSupport :
      ∀ v ∈ good,
        positiveSupport (centreQuotient (C v) t) = 3) :
    2 ^ (n - 1) + 5 * 2 ^ (n - 3)
      ≤
    ∑ v ∈ (Finset.univ.erase top : Finset V),
      2 ^ exponentAfterDeleteTopAt C (by omega : 3 ≤ Fintype.card V) top t v := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  apply five_survivor_weight_ge_six_point_profile_of_four_gains
      (by omega : 3 ≤ n)
      top hcard
      (exponentAfterDeleteTopAt C top t)
      good hgoodSub hgoodCard
  · intro v hvt
    rw [← hMin v hvt]
    exact exponent_le_after_delete_top
      C top htpos.le (by omega : 3 ≤ Fintype.card V) hvt
  · intro v hv
    have hvt : v ≠ top := by
      have hvS := hgoodSub hv
      simpa using (Finset.mem_erase.mp hvS).1
    rw [← hMin v hvt]
    exact exponent_add_one_le_after_delete_top_of_support_three
      hp hcap C
      (by omega : 3 ≤ Fintype.card V)
      (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      top hTop hvt
      (hMin v hvt)
      (hgoodSupport v hv)

#print axioms exponentAfterDeleteTopAt
#print axioms exponent_le_after_delete_top
#print axioms exponent_add_one_le_after_delete_top_of_support_three
#print axioms six_point_top_deletion_compensated_of_four_support_three

end JSP000404Research
