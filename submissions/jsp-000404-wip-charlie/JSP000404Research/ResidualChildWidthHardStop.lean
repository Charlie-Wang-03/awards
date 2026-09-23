
import JSP000404Research.ResidualSideWidthReduction
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Hard stop: the whole not-sink child need not lose one width unit

ResidualBinaryRecursion uses the overlapping children

  Left  = {v | not HighSink(v)},
  Right = {v | not HighSource(v)}.

ResidualSideWidthReduction proves a genuine one-unit width drop on the pure
HighSource set and on the pure HighSink set.  That statement does NOT extend
to the entire not-sink / not-source children.

The exact three-point DirectionData below has

  n = 3, delta = 2/5, width = 17/5,

with increasing-edge values

  D(0,1) = 14/5,
  D(0,2) =  9/5,
  D(1,2) =  1.

It satisfies all DirectionData axioms.  Vertices 0 and 1 are both not high
sinks at threshold n=3, but

  D(0,1) = 14/5 > 12/5 = (n-1)+delta.

Therefore the LeftResidualChild cannot in general be treated as a fresh
DirectionData instance of width (n-1)+delta.  Any recursive closure must use
additional structure (for example source/sink blocks, inactive separators, or
a stronger geometric invariant), not a silent whole-child width reduction.
-/

namespace JSP000404Research
namespace DirectionData

def childWidthHardStopValue : Fin 3 → Fin 3 → ℝ :=
  ![
    ![0, 14/5, 9/5],
    ![0, 0,    1],
    ![0, 0,    0]
  ]

def childWidthHardStopData :
    DirectionData (Fin 3) (17/5 : ℝ) where
  value := childWidthHardStopValue
  nonnegative := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [childWidthHardStopValue] at hij ⊢
  belowWidth := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [childWidthHardStopValue] at hij ⊢
  between := by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [childWidthHardStopValue] at hij hjk ⊢
  middleSeparated := by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [childWidthHardStopValue, abs_of_nonneg, abs_of_nonpos] at hij hjk ⊢
  firstGap := by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [childWidthHardStopValue, abs_of_nonneg, abs_of_nonpos] at hij hjk ⊢
  lastGap := by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [childWidthHardStopValue, abs_of_nonneg, abs_of_nonpos] at hij hjk ⊢

theorem childWidthHardStop_zero_not_sink :
    ¬ HighSink childWidthHardStopData 3 (0 : Fin 3) := by
  rintro ⟨u, hu, _⟩
  have : u.val < 0 := hu
  omega

theorem childWidthHardStop_one_not_sink :
    ¬ HighSink childWidthHardStopData 3 (1 : Fin 3) := by
  rintro ⟨u, hu, hhigh⟩
  fin_cases u <;>
    norm_num [childWidthHardStopData, childWidthHardStopValue] at hu hhigh

theorem childWidthHardStop_pair_not_pred_width :
    ¬ childWidthHardStopData.value (0 : Fin 3) (1 : Fin 3) <
        (3 : ℝ) - 1 + 2/5 := by
  norm_num [childWidthHardStopData, childWidthHardStopValue]

/-- Exact failure of the tempting whole-left-child one-unit-width theorem. -/
theorem notSink_child_pred_width_false :
    ¬ (∀ {u v : Fin 3},
        u < v →
        ¬ HighSink childWidthHardStopData 3 u →
        ¬ HighSink childWidthHardStopData 3 v →
        childWidthHardStopData.value u v <
          (3 : ℝ) - 1 + 2/5) := by
  intro h
  have h01 : (0 : Fin 3) < 1 := by norm_num
  have hlt :=
    h h01
      childWidthHardStop_zero_not_sink
      childWidthHardStop_one_not_sink
  exact childWidthHardStop_pair_not_pred_width hlt

#print axioms childWidthHardStopData
#print axioms notSink_child_pred_width_false

end DirectionData
end JSP000404Research
