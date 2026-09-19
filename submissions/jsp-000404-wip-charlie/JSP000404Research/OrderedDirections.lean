import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic

/-!
# Ordered direction systems

An abstract finite shadow of a planar configuration under a global angle cap.
For every increasing edge `i < j`, `value i j` is its normalized forward
line direction.  The axioms retain only the order/betweenness and the three
angle-gap consequences needed by the current JSP-000404 capacity route.

This module is deliberately independent of the final geometric bridge.
-/

namespace JSP000404Research

/-- Ordered normalized direction data at total width `width`. -/
structure DirectionData (V : Type*) [LinearOrder V] (width : ℝ) where
  value : V → V → ℝ
  nonnegative : ∀ {i j}, i < j → 0 ≤ value i j
  belowWidth : ∀ {i j}, i < j → value i j < width
  between : ∀ {i j k}, i < j → j < k →
    (value i j ≤ value i k ∧ value i k ≤ value j k) ∨
    (value j k ≤ value i k ∧ value i k ≤ value i j)
  middleSeparated : ∀ {i j k}, i < j → j < k →
    1 ≤ |value i j - value j k|
  firstGap : ∀ {i j k}, i < j → j < k →
    |value i j - value i k| ≤ width - 1
  lastGap : ∀ {i j k}, i < j → j < k →
    |value i k - value j k| ≤ width - 1

namespace DirectionData

/-- A triple has one of two linear orientations.  In either orientation the
outer two directions differ by at least one unit while the middle direction
is within `width - 1` of both. -/
theorem triple_constraints
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) {i j k : V}
    (hij : i < j) (hjk : j < k) :
    (D.value i j ≤ D.value i k ∧
      D.value i k ≤ D.value j k ∧
      1 ≤ D.value j k - D.value i j ∧
      D.value i k - D.value i j ≤ width - 1 ∧
      D.value j k - D.value i k ≤ width - 1) ∨
    (D.value j k ≤ D.value i k ∧
      D.value i k ≤ D.value i j ∧
      1 ≤ D.value i j - D.value j k ∧
      D.value i j - D.value i k ≤ width - 1 ∧
      D.value i k - D.value j k ≤ width - 1) := by
  rcases D.between hij hjk with hforward | hreverse
  · left
    have hsep := D.middleSeparated hij hjk
    have hfirst := D.firstGap hij hjk
    have hlast := D.lastGap hij hjk
    rw [abs_of_nonpos (sub_nonpos.2 (hforward.1.trans hforward.2))] at hsep
    rw [abs_of_nonpos (sub_nonpos.2 hforward.1)] at hfirst
    rw [abs_of_nonpos (sub_nonpos.2 hforward.2)] at hlast
    exact ⟨hforward.1, hforward.2, by linarith, by linarith, by linarith⟩
  · right
    have hsep := D.middleSeparated hij hjk
    have hfirst := D.firstGap hij hjk
    have hlast := D.lastGap hij hjk
    rw [abs_of_nonneg (sub_nonneg.2 (hreverse.1.trans hreverse.2))] at hsep
    rw [abs_of_nonneg (sub_nonneg.2 hreverse.2)] at hfirst
    rw [abs_of_nonneg (sub_nonneg.2 hreverse.1)] at hlast
    exact ⟨hreverse.1, hreverse.2, by linarith, by linarith, by linarith⟩

/-- Three ordered vertices already force normalized direction width at least
`3/2`. -/
theorem threePoint_width
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) {v0 v1 v2 : V}
    (h01 : v0 < v1) (h12 : v1 < v2) :
    (3 : ℝ) / 2 ≤ width := by
  rcases triple_constraints D h01 h12 with h | h <;> linarith

/-- Four ordered vertices force normalized direction width at least `2`.

The proof is a finite orientation elimination on the four triples.  This is
the first nontrivial base case for the prospective sharp-capacity recurrence.
-/
theorem fourPoint_width
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) {v0 v1 v2 v3 : V}
    (h01 : v0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) :
    (2 : ℝ) ≤ width := by
  have h02 : v0 < v2 := h01.trans h12
  have h03 : v0 < v3 := h02.trans h23
  have h13 : v1 < v3 := h12.trans h23
  have t012 := triple_constraints D h01 h12
  have t013 := triple_constraints D h01 h13
  have t023 := triple_constraints D h02 h23
  have t123 := triple_constraints D h12 h23
  rcases t012 with t012 | t012 <;>
    rcases t013 with t013 | t013 <;>
    rcases t023 with t023 | t023 <;>
    rcases t123 with t123 | t123 <;> linarith

#print axioms triple_constraints
#print axioms threePoint_width
#print axioms fourPoint_width

end DirectionData
end JSP000404Research
