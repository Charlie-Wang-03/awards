import JSP000404Research.DirectionDataHallExactCycleTight
import Mathlib.Tactic

/-!
# Concrete three-point direction profile: audit of abstract G1 geometry

Values on increasing Fin 3 edges:
  (0,1) -> 21/10; (0,2) -> 19/10; (1,2) -> 1
with width t = 23/10, retained palette size n = 2.

The ordered triple satisfies all six axioms of DirectionData, including
between, middleSeparated, firstGap, and lastGap. The three local cyclic
gap lists have exponents 1,0,0, respectively.

This is a *candidate* for a genuine loss-free minimal Hall-deficient
two-vertex core of the projected completion construction. The latter
claim is NOT made as a theorem here: it requires an explicit
finite Boolean-block calculation and a separate Lean check.
-/

namespace JSP000404Research
namespace DirectionData

private def candidateVal (i j : Fin 3) : ℝ :=
  if i = 0 ∧ j = 1 then (21 : ℝ) / 10
  else if i = 0 ∧ j = 2 then (19 : ℝ) / 10
  else if i = 1 ∧ j = 2 then (1 : ℝ)
  else 0

/-- The numerical three-point profile satisfies the *actual*
DirectionData axioms; this is not merely an edge-colouring toy. -/
noncomputable def candidateThreePointData :
    DirectionData (Fin 3) ((23 : ℝ) / 10) where
  value := candidateVal
  nonnegative := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [candidateVal] at *
  belowWidth := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [candidateVal] at *
  between := by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [candidateVal] at *
  middleSeparated := by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [candidateVal] at *
  firstGap := by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [candidateVal] at *
  lastGap := by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [candidateVal] at *

/-- Exact arithmetic for the three ordered two-ray direction lists:
the first centre is saturated, while the other two are strictly slack. -/
theorem candidateThreePoint_numeric_gap_exponents :
    listExponent
        (linearCyclicGapQuotients ((23 : ℝ) / 10)
          [((19 : ℝ) / 10), ((21 : ℝ) / 10)]) = 1 ∧
    listExponent
        (linearCyclicGapQuotients ((23 : ℝ) / 10)
          [(1 : ℝ), ((21 : ℝ) / 10)]) = 0 ∧
    listExponent
        (linearCyclicGapQuotients ((23 : ℝ) / 10)
          [(1 : ℝ), ((19 : ℝ) / 10)]) = 0 := by
  norm_num [linearCyclicGapQuotients, successiveDiffsFrom,
    listExponent, excess]

#print axioms candidateThreePoint_numeric_gap_exponents

end DirectionData
end JSP000404Research
