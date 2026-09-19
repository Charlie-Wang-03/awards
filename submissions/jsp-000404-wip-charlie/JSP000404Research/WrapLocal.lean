import JSP000404Research.OrderedDirections
import Mathlib.Tactic

/-!
# Local rules for a wrap direction band

Fix normalized direction width `width = n + delta`.  The prospective merged
wrap colour consists of the low component `[0,1)` and the high component
`[n,width)`; the ordinary middle directions lie in `[1,n)`.

The lemmas here isolate the local L/H constraints forced by
`DirectionData`.

* At a vertex lying between its two neighbours in the ambient linear order,
  two wrap edges cannot have the same component: the two adjacent directions
  are separated by at least one unit, while each component has width < 1.
* At a local minimum (or maximum) of a triangle-free wrap cycle, the two wrap
  edges must have the same component, because the chord between the two
  neighbours is a middle direction and the third direction lies between the
  other two.

These are the local parity rules behind the current wrap-band odd-cycle route.
-/

namespace JSP000404Research
namespace DirectionData

/-- Low component of the merged wrap band. -/
def IsLow {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (i j : V) : Prop :=
  D.value i j < 1

/-- High component of the merged wrap band, starting at the integer threshold
`n`. -/
def IsHigh {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) (i j : V) : Prop :=
  (n : ℝ) ≤ D.value i j

/-- Ordinary middle band between the two wrap components. -/
def IsMiddle {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) (i j : V) : Prop :=
  1 ≤ D.value i j ∧ D.value i j < n

/-- Two consecutive low wrap edges are impossible. -/
theorem not_low_low_at_middle
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width)
    {a v b : V} (hav : a < v) (hvb : v < b)
    (havLow : IsLow D a v) (hvbLow : IsLow D v b) :
    False := by
  have hsep := D.middleSeparated hav hvb
  unfold IsLow at havLow hvbLow
  have hsmall : |D.value a v - D.value v b| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [D.nonnegative hav, D.nonnegative hvb]
  exact (not_lt_of_ge hsep) hsmall

/-- Two consecutive high wrap edges are impossible whenever the high component
has width < 1. -/
theorem not_high_high_at_middle
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {a v b : V} (hav : a < v) (hvb : v < b)
    (havHigh : IsHigh D n a v) (hvbHigh : IsHigh D n v b) :
    False := by
  have hsep := D.middleSeparated hav hvb
  unfold IsHigh at havHigh hvbHigh
  have haTop := D.belowWidth hav
  have hbTop := D.belowWidth hvb
  rw [hwidth] at haTop hbTop
  have hsmall : |D.value a v - D.value v b| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  exact (not_lt_of_ge hsep) hsmall

/-- At an ambient-order middle vertex, two wrap edges therefore have opposite
components.  The statement is given in disjunctive form so it can be used
without committing to a particular Boolean encoding. -/
theorem wrap_opposite_at_middle
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {a v b : V} (hav : a < v) (hvb : v < b)
    (havWrap : IsLow D a v ∨ IsHigh D n a v)
    (hvbWrap : IsLow D v b ∨ IsHigh D n v b) :
    (IsLow D a v ∧ IsHigh D n v b) ∨
      (IsHigh D n a v ∧ IsLow D v b) := by
  rcases havWrap with havLow | havHigh <;>
    rcases hvbWrap with hvbLow | hvbHigh
  · exact False.elim (not_low_low_at_middle D hav hvb havLow hvbLow)
  · exact Or.inl ⟨havLow, hvbHigh⟩
  · exact Or.inr ⟨havHigh, hvbLow⟩
  · exact False.elim
      (not_high_high_at_middle D hwidth hdelta hav hvb havHigh hvbHigh)

/-- Local-minimum rule: if `m<a<b`, the two edges from the local minimum
`m` are wrap edges, while the chord `a-b` is a middle edge, then the two
wrap edges belong to the same component. -/
theorem wrap_same_at_local_min
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    {m a b : V} (hma : m < a) (hab : a < b)
    (hmaWrap : IsLow D m a ∨ IsHigh D n m a)
    (hmbWrap : IsLow D m b ∨ IsHigh D n m b)
    (habMid : IsMiddle D n a b) :
    (IsLow D m a ∧ IsLow D m b) ∨
      (IsHigh D n m a ∧ IsHigh D n m b) := by
  have hbetween := D.between hma hab
  unfold IsLow IsHigh IsMiddle at *
  rcases hmaWrap with hmaLow | hmaHigh <;>
    rcases hmbWrap with hmbLow | hmbHigh
  · exact Or.inl ⟨hmaLow, hmbLow⟩
  · rcases hbetween with h | h <;> linarith
  · rcases hbetween with h | h <;> linarith
  · exact Or.inr ⟨hmaHigh, hmbHigh⟩

/-- Local-maximum rule, symmetric to `wrap_same_at_local_min`. -/
theorem wrap_same_at_local_max
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    {a b m : V} (hab : a < b) (hbm : b < m)
    (hamWrap : IsLow D a m ∨ IsHigh D n a m)
    (hbmWrap : IsLow D b m ∨ IsHigh D n b m)
    (habMid : IsMiddle D n a b) :
    (IsLow D a m ∧ IsLow D b m) ∨
      (IsHigh D n a m ∧ IsHigh D n b m) := by
  have hbetween := D.between hab hbm
  unfold IsLow IsHigh IsMiddle at *
  rcases hamWrap with hamLow | hamHigh <;>
    rcases hbmWrap with hbmLow | hbmHigh
  · exact Or.inl ⟨hamLow, hbmLow⟩
  · rcases hbetween with h | h <;> linarith
  · rcases hbetween with h | h <;> linarith
  · exact Or.inr ⟨hamHigh, hbmHigh⟩

#print axioms not_low_low_at_middle
#print axioms not_high_high_at_middle
#print axioms wrap_opposite_at_middle
#print axioms wrap_same_at_local_min
#print axioms wrap_same_at_local_max

end DirectionData
end JSP000404Research
