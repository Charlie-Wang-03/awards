import JSP000404Research.OrderedBandCode
import JSP000404Research.FiniteProjectiveRays
import Mathlib.Tactic

/-!
# Lightweight incident local direction value

This module contains only the unoriented incident direction coordinate and its
basic [0,t) bounds.  It is separated from LocalDirectionCycle so local
projection geometry does not inherit the full linear band-capacity proof.
-/

namespace JSP000404Research
namespace DirectionData

def localDirectionValue
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) (j : OtherVertex i) : ℝ :=
  if h : j.1 < i then
    D.value j.1 i
  else
    D.value i j.1

theorem localDirectionValue_nonneg
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) (j : OtherVertex i) :
    0 ≤ D.localDirectionValue i j := by
  unfold localDirectionValue
  by_cases hji : j.1 < i
  · simp [hji, D.nonnegative hji]
  · have hij : i < j.1 := by
      have hle : i ≤ j.1 := le_of_not_gt hji
      exact lt_of_le_of_ne hle j.2.symm
    simp [hji, D.nonnegative hij]

theorem localDirectionValue_lt
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) (j : OtherVertex i) :
    D.localDirectionValue i j < t := by
  unfold localDirectionValue
  by_cases hji : j.1 < i
  · simp [hji, D.belowWidth hji]
  · have hij : i < j.1 := by
      have hle : i ≤ j.1 := le_of_not_gt hji
      exact lt_of_le_of_ne hle j.2.symm
    simp [hji, D.belowWidth hij]

#print axioms localDirectionValue_nonneg
#print axioms localDirectionValue_lt

end DirectionData
end JSP000404Research
