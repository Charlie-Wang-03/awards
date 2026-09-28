import JSP000404Research.CutLocalBandCycle
import JSP000404Research.LinearCyclicDeletionGain
import Mathlib.Tactic

/-!
# Concrete centre-exponent gain from cut-normalized parent/child value lists

CutLocalBandCycle identifies the cyclic floor-gap exponent of every arbitrary
projective-cut ray cycle with the canonical centreExponent.

Therefore deletion gain can be proved entirely in a convenient cut
representation.

This file packages the final arithmetic transport:

* if the parent cut values are a :: b :: c :: xs,
* the child cut values are a :: c :: xs,
* and the two parent floor gaps beside b are positive,

then the actual child centreExponent is at least one larger.

A final-position version is also supplied.

The remaining geometric adapter only has to show that restrictDelete removes
the selected ray from the cut-sorted value list.
-/

namespace JSP000404Research

namespace CentreCutRayCycle

theorem centreExponent_gain_of_normalizedValues_delete_second
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    {C : CentreProjectiveCycle hp i}
    {c t : ℝ}
    (R : CentreCutRayCycle hp C c)
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (D := C.restrictDelete r hir hother)
    (Rc :
      CentreCutRayCycle
        (restrictedPoint_injective hp r) D c)
    (ht : 0 < t)
    {a b d : ℝ} {xs : List ℝ}
    (hParent :
      R.normalizedValues t = a :: b :: d :: xs)
    (hChild :
      Rc.normalizedValues t = a :: d :: xs)
    (hab : a ≤ b)
    (hbd : b ≤ d)
    (hLeft : 1 ≤ Nat.floor (b - a))
    (hRight : 1 ≤ Nat.floor (d - b)) :
    centreExponent C t + 1 ≤
      centreExponent D t := by
  have hgain :=
    listExponent_linearCyclic_delete_second_gain
      (t := t) (a := a) (b := b) (c := d) (xs := xs)
      hab hbd hLeft hRight
  have hParentExp :
      listExponent
          (linearCyclicGapQuotients t
            (R.normalizedValues t))
        =
      centreExponent C t := by
    simpa [CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients] using
      R.exponent_eq_centreExponent hp ht
  have hChildExp :
      listExponent
          (linearCyclicGapQuotients t
            (Rc.normalizedValues t))
        =
      centreExponent D t := by
    simpa [CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients] using
      Rc.exponent_eq_centreExponent
        (restrictedPoint_injective hp r) ht
  rw [hParent, hChild] at hParentExp hChildExp
  rw [← hParentExp, ← hChildExp]
  exact hgain

theorem centreExponent_gain_of_normalizedValues_delete_last
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    {C : CentreProjectiveCycle hp i}
    {c t : ℝ}
    (R : CentreCutRayCycle hp C c)
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (D := C.restrictDelete r hir hother)
    (Rc :
      CentreCutRayCycle
        (restrictedPoint_injective hp r) D c)
    (ht : 0 < t)
    {a z : ℝ} {pre : List ℝ}
    (hParent :
      R.normalizedValues t = a :: (pre ++ [z]))
    (hChild :
      Rc.normalizedValues t = a :: pre)
    (hpre : pre ≠ [])
    (hLeft :
      1 ≤ Nat.floor (z - pre.getLastD a))
    (hWrap :
      1 ≤ Nat.floor (a + t - z))
    (horder :
      pre.getLastD a ≤ z)
    (hwrap0 :
      0 ≤ a + t - z) :
    centreExponent C t + 1 ≤
      centreExponent D t := by
  have hgain :=
    listExponent_linearCyclic_delete_last_gain
      (t := t) (a := a) (z := z) (pre := pre)
      hpre hLeft hWrap horder hwrap0
  have hParentExp :
      listExponent
          (linearCyclicGapQuotients t
            (R.normalizedValues t))
        =
      centreExponent C t := by
    simpa [CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients] using
      R.exponent_eq_centreExponent hp ht
  have hChildExp :
      listExponent
          (linearCyclicGapQuotients t
            (Rc.normalizedValues t))
        =
      centreExponent D t := by
    simpa [CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients] using
      Rc.exponent_eq_centreExponent
        (restrictedPoint_injective hp r) ht
  rw [hParent, hChild] at hParentExp hChildExp
  rw [← hParentExp, ← hChildExp]
  exact hgain

#print axioms CentreCutRayCycle.centreExponent_gain_of_normalizedValues_delete_second
#print axioms CentreCutRayCycle.centreExponent_gain_of_normalizedValues_delete_last

end CentreCutRayCycle
end JSP000404Research
