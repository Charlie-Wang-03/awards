import JSP000404Research.StandardResidualInterval
import Mathlib.Tactic

/-!
# Residual-edge triangle: the opposite child is below half the penultimate band

For normalized direction width t=n+delta with delta<1/2,
consider three ordered vertices u<x<v and an outer residual edge uv.

Exactly one child edge ux or xv is residual (existing interval theorem).
The direction data triangle constraints give an actual >=1 difference
between the two child directions. Since the residual child's direction
is strictly below t=n+delta, the opposite child has direction

    lowChild < n - 1 + delta < n - 1/2.

This is a quantitative half-band geometric gap. Merely saying the
opposite child is non-residual (<n) discards a full half band of
information. The result holds for genuine DirectionData, and is
subsequently usable by the true planar generic-projection bridge.

It does not itself pay any global projected-completion defect.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- Every middle point inside a residual edge determines a unique
residual child. The other child has normalized direction below n-1/2,
and the child-direction gap is at least one full normalized unit. -/
theorem standardResidual_intermediate_forces_subhalf_opposite_child
    {V : Type*} [LinearOrder V]
    {t delta : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hwidth : t < (n + 1 : ℕ))
    {u x v : V}
    (hux : u < x)
    (hxv : x < v)
    (hres : IsResidual (standardResidualColoring D n hwidth) u v) :
    (
      IsResidual (standardResidualColoring D n hwidth) u x ∧
        ¬ IsResidual (standardResidualColoring D n hwidth) x v ∧
        D.value x v + 1 ≤ D.value u x ∧
        D.value x v + (1 : ℝ) / 2 < (n : ℝ)
    ) ∨
    (
      ¬ IsResidual (standardResidualColoring D n hwidth) u x ∧
        IsResidual (standardResidualColoring D n hwidth) x v ∧
        D.value u x + 1 ≤ D.value x v ∧
        D.value u x + (1 : ℝ) / 2 < (n : ℝ)
    ) := by
  have hsplit :=
    standardResidual_intermediate_exactly_one
      D hwidth hux hxv hres
  have htri := triple_constraints D hux hxv
  rcases hsplit with ⟨hleft, hnotRight⟩ | ⟨hnotLeft, hright⟩
  · left
    have hbound : D.value u x < t := D.belowWidth hux
    rcases htri with hforward | hreverse
    · have hlow : (n : ℝ) ≤ D.value u x :=
        (standardResidual_iff_high D n hwidth hux).1 hleft
      have hrightHigh : (n : ℝ) ≤ D.value x v :=
        hlow.trans (hforward.1.trans hforward.2)
      exact False.elim (hnotRight
        ((standardResidual_iff_high D n hwidth hxv).2 hrightHigh))
    · have hsep : 1 ≤ D.value u x - D.value x v :=
        hreverse.2.2.1
      exact ⟨hleft, hnotRight, by linarith, by rw [ht] at hbound; linarith⟩
  · right
    have hbound : D.value x v < t := D.belowWidth hxv
    rcases htri with hforward | hreverse
    · have hsep : 1 ≤ D.value x v - D.value u x :=
        hforward.2.2.1
      exact ⟨hnotLeft, hright, by linarith, by rw [ht] at hbound; linarith⟩
    · have hhigh : (n : ℝ) ≤ D.value x v :=
        (standardResidual_iff_high D n hwidth hxv).1 hright
      have hleftHigh : (n : ℝ) ≤ D.value u x :=
        hhigh.trans (hreverse.1.trans hreverse.2)
      exact False.elim (hnotLeft
        ((standardResidual_iff_high D n hwidth hux).2 hleftHigh))

#print axioms standardResidual_intermediate_forces_subhalf_opposite_child

end DirectionData
end JSP000404Research
