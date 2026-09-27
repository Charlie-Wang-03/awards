import JSP000404Research.CyclicTransitionUnitGapSlot
import JSP000404Research.StableCyclicSupport
import JSP000404Research.SixPointThirdLayerTerminal
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Canonical positive quotient-gap slots

The q=1 critical-transition phase argument uses GlobalUnitGapSlot.  Saturated
last-merge failures can instead be carried by a canonical quotient q>=2.
This file introduces the common cut-independent universe of every positive
canonical quotient coordinate.

A slot records only

  centre, cyclic gap index, proof q>0.

Its canonical normalized start is the normalized direction of the ray at the
same cyclic index; its scaled length is t times the corresponding normalized
projective gap.  The quotient is definitionally the natural floor of this
scaled length.

The slot cardinality at one centre is exactly positiveSupport.  In the
six-point top + five n-3 terminal, the top contributes at most one positive
slot and every minimum contributes at most three, hence there are at most
sixteen positive slots globally.
-/

namespace JSP000404Research

open scoped BigOperators

abbrev CentrePositiveGap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :=
  {r : Fin C.gaps.length // centreQuotient C t r ≠ 0}

abbrev GlobalPositiveGapSlot
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ) :=
  Σ i : V, CentrePositiveGap (C i) t

def centrePositiveGapQuotient
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentrePositiveGap C t) : ℕ :=
  centreQuotient C t u.1

def centrePositiveGapStart
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentrePositiveGap C t) : ℝ :=
  normalizedRayTheta hp t i
    (C.rays.get (gapToRayIndex C u.1))

def centrePositiveGapScaledLength
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentrePositiveGap C t) : ℝ :=
  t * C.gaps.get u.1

def globalPositiveGapQuotient
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalPositiveGapSlot C t) : ℕ :=
  centrePositiveGapQuotient (C u.1) t u.2

def globalPositiveGapStart
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalPositiveGapSlot C t) : ℝ :=
  centrePositiveGapStart (C u.1) t u.2

def globalPositiveGapScaledLength
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalPositiveGapSlot C t) : ℝ :=
  centrePositiveGapScaledLength (C u.1) t u.2

@[simp] theorem centrePositiveGapQuotient_eq_floor
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentrePositiveGap C t) :
    centrePositiveGapQuotient C t u =
      Nat.floor (centrePositiveGapScaledLength C t u) := by
  rfl

theorem centrePositiveGapQuotient_pos
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentrePositiveGap C t) :
    1 ≤ centrePositiveGapQuotient C t u := by
  exact Nat.one_le_iff_ne_zero.mpr u.2

theorem centrePositiveGap_card_eq_positiveSupport
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    Fintype.card (CentrePositiveGap C t) =
      positiveSupport (centreQuotient C t) := by
  classical
  let S : Finset (Fin C.gaps.length) :=
    Finset.univ.filter
      (fun r => centreQuotient C t r ≠ 0)
  have hcard :
      Fintype.card (CentrePositiveGap C t) = S.card := by
    apply Fintype.subtype_card S
    intro r
    simp [S]
  rw [hcard]
  simpa [S] using
    (positiveIndexSet_card_eq_positiveSupport
      (centreQuotient C t)).symm

theorem globalPositiveGapSlot_card_eq_sum_positiveSupport
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ) :
    Fintype.card (GlobalPositiveGapSlot C t) =
      ∑ i : V, positiveSupport (centreQuotient (C i) t) := by
  classical
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact centrePositiveGap_card_eq_positiveSupport (C i) t

theorem centre_positiveSupport_le_one_of_exponent_n_sub_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 1) :
    positiveSupport (centreQuotient C t) ≤ 1 := by
  have hsum :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega) hdelta0 hdelta1 ht
  have h :=
    positiveSupport_le_deficit
      (centreQuotient C t) n hsum
  rw [← show floorExcess (centreQuotient C t) =
      centreExponent C t by rfl, hexp] at h
  omega

theorem centre_positiveSupport_le_three_of_exponent_n_sub_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3) :
    positiveSupport (centreQuotient C t) ≤ 3 := by
  have hsum :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega) hdelta0 hdelta1 ht
  have h :=
    positiveSupport_le_deficit
      (centreQuotient C t) n hsum
  rw [← show floorExcess (centreQuotient C t) =
      centreExponent C t by rfl, hexp] at h
  omega

theorem six_point_globalPositiveGapSlot_card_le_sixteen
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3) :
    Fintype.card (GlobalPositiveGapSlot C t) ≤ 16 := by
  rw [globalPositiveGapSlot_card_eq_sum_positiveSupport C t]
  have htop :
      positiveSupport (centreQuotient (C top) t) ≤ 1 :=
    centre_positiveSupport_le_one_of_exponent_n_sub_one
      (C top) hn hdelta0 hdelta1 ht hTop
  have hother :
      ∀ i : V, i ≠ top →
        positiveSupport (centreQuotient (C i) t) ≤ 3 := by
    intro i hit
    exact centre_positiveSupport_le_three_of_exponent_n_sub_three
      (C i) hn hdelta0 hdelta1 ht (hMin i hit)
  calc
    (∑ i : V,
      positiveSupport (centreQuotient (C i) t))
      =
      positiveSupport (centreQuotient (C top) t) +
        ∑ i ∈ (Finset.univ.erase top),
          positiveSupport (centreQuotient (C i) t) := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ top)]
            simp [add_comm]
    _ ≤
      1 + ∑ _i ∈ (Finset.univ.erase top), 3 := by
        apply Nat.add_le_add htop
        apply Finset.sum_le_sum
        intro i hi
        exact hother i (Finset.mem_erase.mp hi).1
    _ = 16 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ top)]
        simp [hcard]

#print axioms centrePositiveGap_card_eq_positiveSupport
#print axioms globalPositiveGapSlot_card_eq_sum_positiveSupport
#print axioms six_point_globalPositiveGapSlot_card_le_sixteen

end JSP000404Research
