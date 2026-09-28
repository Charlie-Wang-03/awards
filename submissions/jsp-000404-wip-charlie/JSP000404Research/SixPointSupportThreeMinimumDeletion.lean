import JSP000404Research.SupportThreeMiddleOrDeletionGain
import JSP000404Research.SixPointMinimumDeletionWeight
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

/-!
# Concrete compensated deletion from a non-middle support-three centre

Define the concrete exponent profile after deleting an arbitrary vertex r:

  exponentAfterDeleteAt C r t v

is the actual exponent of the restricted centre at v when v survives, and zero
at r itself.

For the six-point 1+5 terminal profile, deletion is monotone at every survivor.
By SixPointMinimumDeletionWeight, deleting a minimum is fully compensated as
soon as one other minimum gains one exponent unit.

SupportThreeMiddleOrDeletionGain supplies exactly such a unit gain whenever a
support-three minimum is not in the middle-hidden pinned shape.

Hence every six-point support-three minimum satisfies the global dichotomy:

* middle-hidden pinned shape; or
* an explicitly compensated deletion of some non-top minimum.

Consequently, any minimal-counterexample branch with no compensated minimum
deletion forces every support-three minimum into the single middle-hidden
shape.
-/

namespace JSP000404Research

open scoped BigOperators

noncomputable def exponentAfterDeleteAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard3 : 3 ≤ Fintype.card V)
    (deleted : V)
    (t : ℝ)
    (v : V) : ℕ :=
  if h : v ≠ deleted then
    let hother :=
      child_other_nonempty_of_card_ge_three
        hcard3 h
    centreExponent
      ((C v).restrictDelete deleted h hother) t
  else 0

theorem exponent_le_after_delete_at
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard3 : 3 ≤ Fintype.card V)
    (deleted : V)
    {t : ℝ}
    (ht0 : 0 ≤ t)
    {v : V}
    (hvd : v ≠ deleted) :
    centreExponent (C v) t ≤
      exponentAfterDeleteAt C hcard3 deleted t v := by
  unfold exponentAfterDeleteAt
  rw [dif_pos hvd]
  dsimp only
  let hother :=
    child_other_nonempty_of_card_ge_three
      hcard3 hvd
  exact centreExponent_mono_restrictDelete
    (C v) hvd hother ht0

theorem exponent_add_one_le_after_delete_at
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard3 : 3 ≤ Fintype.card V)
    (deleted : V)
    {t : ℝ}
    {v : V}
    (hvd : v ≠ deleted)
    (hgain :
      let hother :=
        child_other_nonempty_of_card_ge_three
          hcard3 hvd
      centreExponent (C v) t + 1 ≤
        centreExponent
          ((C v).restrictDelete deleted hvd hother) t) :
    centreExponent (C v) t + 1 ≤
      exponentAfterDeleteAt C hcard3 deleted t v := by
  unfold exponentAfterDeleteAt
  rw [dif_pos hvd]
  exact hgain

/-- One concrete unit gain at a surviving minimum compensates deletion of any
other minimum in the six-point terminal profile. -/
theorem six_point_concrete_minimum_deletion_compensated_of_one_gain
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 3 ≤ n)
    (ht0 : 0 ≤ t)
    (top deleted gain : V)
    (hdelTop : deleted ≠ top)
    (hgainDel : gain ≠ deleted)
    (hgainTop : gain ≠ top)
    (hTop :
      centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hgain :
      let hother :=
        child_other_nonempty_of_card_ge_three
          (by rw [hcard]; omega) hgainDel
      centreExponent (C gain) t + 1 ≤
        centreExponent
          ((C gain).restrictDelete
            deleted hgainDel hother) t) :
    2 ^ (n - 1) + 5 * 2 ^ (n - 3)
      ≤
    ∑ v ∈ (Finset.univ.erase deleted : Finset V),
      2 ^
        exponentAfterDeleteAt C
          (by rw [hcard]; omega)
          deleted t v := by
  let hcard3 : 3 ≤ Fintype.card V := by
    rw [hcard]
    omega
  let childExponent :=
    exponentAfterDeleteAt C hcard3 deleted t

  have hTopChild :
      n - 1 ≤ childExponent top := by
    rw [← hTop]
    exact exponent_le_after_delete_at
      C hcard3 deleted ht0 hdelTop.symm

  have hbase :
      ∀ v : V, v ≠ deleted → v ≠ top →
        n - 3 ≤ childExponent v := by
    intro v hvd hvt
    rw [← hMin v hvt]
    exact exponent_le_after_delete_at
      C hcard3 deleted ht0 hvd

  have hgainChild :
      n - 2 ≤ childExponent gain := by
    have hg :
        centreExponent (C gain) t + 1 ≤
          childExponent gain :=
      exponent_add_one_le_after_delete_at
        C hcard3 deleted hgainDel hgain
    rw [hMin gain hgainTop] at hg
    omega

  exact
    five_survivor_weight_ge_six_point_profile_of_one_minimum_gain
      hn top deleted gain hcard
      hdelTop hgainDel hgainTop
      childExponent hTopChild hbase hgainChild

/-- Main global reduction: a support-three minimum is either middle-hidden or
already yields a compensated non-top deletion. -/
theorem six_point_support_three_middle_or_compensated_minimum_deletion
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
    (hTop :
      centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    {i : V}
    (hit : i ≠ top)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = 3) :
    SupportThreePinnedMiddleShape hp hit.symm (C i)
      ∨
    ∃ deleted : V,
      deleted ≠ top ∧
      2 ^ (n - 1) + 5 * 2 ^ (n - 3)
        ≤
      ∑ v ∈ (Finset.univ.erase deleted : Finset V),
        2 ^
          exponentAfterDeleteAt C
            (by rw [hcard]; omega)
            deleted t v := by
  have hdelta1 : delta < 1 := by linarith
  have hsharp :
      SharpAt p delta lam top :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      top (C top) hTop
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht

  rcases support_three_pinned_middle_or_nonTop_deletion_gain
      hp hcap hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hit.symm hsharp (C i) (hMin i hit) hsupport
    with hmiddle | ⟨deleted, hir, hdelTop, hgain⟩
  · exact Or.inl hmiddle
  · right
    have hgainTop : i ≠ top := hit
    have hgainDel : i ≠ deleted := hir
    have hcomp :=
      six_point_concrete_minimum_deletion_compensated_of_one_gain
        C hcard (by omega : 3 ≤ n) htpos.le
        top deleted i hdelTop
        hgainDel hgainTop hTop hMin hgain
    exact ⟨deleted, hdelTop, hcomp⟩

#print axioms exponentAfterDeleteAt
#print axioms exponent_le_after_delete_at
#print axioms exponent_add_one_le_after_delete_at
#print axioms six_point_concrete_minimum_deletion_compensated_of_one_gain
#print axioms six_point_support_three_middle_or_compensated_minimum_deletion

end JSP000404Research
