import JSP000404Research.SixPointUnitGapBudget
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Concrete global unit-gap slot type

A terminal critical obstruction is ultimately an adjacent centre gap with
quotient one.  Package such a location as

  (centre, gap-index, proof quotient=1).

The cardinality of this dependent sigma type is exactly the sum of the
per-centre unitSupport counts.  Therefore the six-point top + five-minimum
terminal has at most ten concrete unit-gap slots.

This removes the need to overcount all global projective edge directions.
-/

namespace JSP000404Research

open scoped BigOperators

abbrev CentreUnitGap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :=
  {r : Fin C.gaps.length // centreQuotient C t r = 1}

abbrev GlobalUnitGapSlot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ) :=
  Σ i : V, CentreUnitGap (C i) t

theorem unitSupport_eq_filter_card
    {I : Type*} [Fintype I]
    (q : I → ℕ) :
    unitSupport q =
      ((Finset.univ : Finset I).filter
        (fun i => q i = 1)).card := by
  classical
  unfold unitSupport
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  rfl

theorem centreUnitGap_card_eq_unitSupport
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    Fintype.card (CentreUnitGap C t) =
      unitSupport (centreQuotient C t) := by
  classical
  let S : Finset (Fin C.gaps.length) :=
    Finset.univ.filter
      (fun r => centreQuotient C t r = 1)
  have hcard :
      Fintype.card (CentreUnitGap C t) = S.card := by
    apply Fintype.subtype_card S
    intro r
    simp [S]
  rw [hcard]
  symm
  simpa [S] using
    unitSupport_eq_filter_card (centreQuotient C t)

theorem globalUnitGapSlot_card_eq_sum_unitSupport
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ) :
    Fintype.card (GlobalUnitGapSlot C t) =
      ∑ i : V, unitSupport (centreQuotient (C i) t) := by
  classical
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact centreUnitGap_card_eq_unitSupport (C i) t

theorem six_point_globalUnitGapSlot_card_le_ten
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (s : V)
    (hTop : centreExponent (C s) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ s →
        centreExponent (C i) t = n - 3) :
    Fintype.card (GlobalUnitGapSlot C t) ≤ 10 := by
  rw [globalUnitGapSlot_card_eq_sum_unitSupport C t]
  exact six_point_top_five_minima_unitSupport_sum_le_ten
    C hn hdelta0 hdelta1 ht hcard s hTop hMin

#print axioms unitSupport_eq_filter_card
#print axioms centreUnitGap_card_eq_unitSupport
#print axioms globalUnitGapSlot_card_eq_sum_unitSupport
#print axioms six_point_globalUnitGapSlot_card_le_ten

end JSP000404Research
