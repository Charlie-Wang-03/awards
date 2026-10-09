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

private noncomputable def candidateVal (i j : Fin 3) : ℝ :=
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
  have hf01 : Nat.floor ((1 : ℝ) / 5) = 0 := by
    apply (Nat.floor_eq_iff (by norm_num)).2
    norm_num
  have hf21 : Nat.floor ((21 : ℝ) / 10) = 2 := by
    apply (Nat.floor_eq_iff (by norm_num)).2
    norm_num
  have hf11 : Nat.floor ((11 : ℝ) / 10) = 1 := by
    apply (Nat.floor_eq_iff (by norm_num)).2
    norm_num
  have hf6 : Nat.floor ((6 : ℝ) / 5) = 1 := by
    apply (Nat.floor_eq_iff (by norm_num)).2
    norm_num
  have hf9 : Nat.floor ((9 : ℝ) / 10) = 0 := by
    apply (Nat.floor_eq_iff (by norm_num)).2
    norm_num
  have hf7 : Nat.floor ((7 : ℝ) / 5) = 1 := by
    apply (Nat.floor_eq_iff (by norm_num)).2
    norm_num
  have hf01inv : Nat.floor ((5 : ℝ)⁻¹) = 0 := by
    simpa [one_div] using hf01
  norm_num [linearCyclicGapQuotients, successiveDiffsFrom,
    listExponent, excess]
  simp [hf01inv, hf21, hf11, hf6, hf9, hf7]


/-- Explicit increasing-value ray order at vertex 0. -/
noncomputable def candidateCycleZero :
    LocalDirectionCycle candidateThreePointData (0 : Fin 3) where
  rays := [⟨2, by decide⟩, ⟨1, by decide⟩]
  complete := by decide
  nodup := by decide
  nonempty := by decide
  value_sorted := by
    norm_num [List.Pairwise, localDirectionValue,
      candidateThreePointData, candidateVal]

/-- Explicit increasing-value ray order at vertex 1. -/
noncomputable def candidateCycleOne :
    LocalDirectionCycle candidateThreePointData (1 : Fin 3) where
  rays := [⟨2, by decide⟩, ⟨0, by decide⟩]
  complete := by decide
  nodup := by decide
  nonempty := by decide
  value_sorted := by
    norm_num [List.Pairwise, localDirectionValue,
      candidateThreePointData, candidateVal]

/-- Explicit increasing-value ray order at vertex 2. -/
noncomputable def candidateCycleTwo :
    LocalDirectionCycle candidateThreePointData (2 : Fin 3) where
  rays := [⟨1, by decide⟩, ⟨0, by decide⟩]
  complete := by decide
  nodup := by decide
  nonempty := by decide
  value_sorted := by
    norm_num [List.Pairwise, localDirectionValue,
      candidateThreePointData, candidateVal]

noncomputable def candidateThreeCycles (i : Fin 3) :
    LocalDirectionCycle candidateThreePointData i :=
  match i with
  | 0 => candidateCycleZero
  | 1 => candidateCycleOne
  | 2 => candidateCycleTwo

theorem candidateThreePoint_cycle_values :
    (candidateThreeCycles 0).values =
        [((19 : ℝ) / 10), ((21 : ℝ) / 10)] ∧
    (candidateThreeCycles 1).values =
        [(1 : ℝ), ((21 : ℝ) / 10)] ∧
    (candidateThreeCycles 2).values =
        [(1 : ℝ), ((19 : ℝ) / 10)] := by
  norm_num [candidateThreeCycles, candidateCycleZero,
    candidateCycleOne, candidateCycleTwo,
    LocalDirectionCycle.values, localDirectionValue,
    candidateThreePointData, candidateVal]

theorem candidateThreePoint_cycles_exponents :
    (candidateThreeCycles 0).exponent = 1 ∧
    (candidateThreeCycles 1).exponent = 0 ∧
    (candidateThreeCycles 2).exponent = 0 := by
  have hvals := candidateThreePoint_cycle_values
  unfold LocalDirectionCycle.exponent LocalDirectionCycle.gapQuotients
  rw [hvals.1, hvals.2.1, hvals.2.2]
  exact candidateThreePoint_numeric_gap_exponents

#print axioms candidateThreePoint_cycles_exponents


/-- Both endpoints of the high-band edge retain precisely band 1. -/
theorem candidateThreePoint_retainedActive_01 :
    retainedActive
        (standardResidualColoring candidateThreePointData 2 (by norm_num))
        (0 : Fin 3) = ({(1 : Fin 2)} : Finset (Fin 2)) ∧
    retainedActive
        (standardResidualColoring candidateThreePointData 2 (by norm_num))
        (1 : Fin 3) = ({(1 : Fin 2)} : Finset (Fin 2)) := by
  classical
  constructor
  · rw [standardResidual_retainedActive_eq_incidentBands]
    ext c
    fin_cases c <;>
      norm_num [incidentBands, candidateThreePointData, candidateVal,
        Fin.exists_fin_succ]
  · rw [standardResidual_retainedActive_eq_incidentBands]
    ext c
    fin_cases c <;>
      norm_num [incidentBands, candidateThreePointData, candidateVal,
        Fin.exists_fin_succ]

#print axioms candidateThreePoint_retainedActive_01

#print axioms candidateThreePoint_numeric_gap_exponents

end DirectionData
end JSP000404Research
