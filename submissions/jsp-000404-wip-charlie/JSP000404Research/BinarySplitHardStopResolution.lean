import JSP000404Research.BinaryGainSplit
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# The four-point deletion hard stop is solved by a binary split

The compensated-deletion hard-stop profile has old exponents

  (0,1,1,1),

so old dyadic mass is 7.

For the simple integer geometric realization, restricting to either side of
any 2+2 split at the same fixed Sendov parameter gives exponent 2 at both
survivors.  Thus every survivor gains at least one exponent unit, while each
two-point child has post-weight

  2^2 + 2^2 = 8 = 2^3.

This is exactly the situation covered by BinaryGainSplit.  Hence the same
configuration which falsifies unconditional single deletion is a positive
regression test for recursive binary splitting.
-/

namespace JSP000404Research

open scoped BigOperators

def hardStopOldExp : Fin 4 → ℕ :=
  ![0,1,1,1]

def hardStopLeftPair : Finset (Fin 4) :=
  {0,1}

def hardStopRightPair : Finset (Fin 4) :=
  {2,3}

def hardStopPairPostExp (_ : Fin 4) : ℕ := 2

theorem hardStop_pair_partition :
    Disjoint hardStopLeftPair hardStopRightPair ∧
      hardStopLeftPair ∪ hardStopRightPair = Finset.univ := by
  native_decide

theorem hardStop_pair_gain_left :
    ∀ v ∈ hardStopLeftPair,
      hardStopOldExp v + 1 ≤ hardStopPairPostExp v := by
  intro v hv
  fin_cases v <;> native_decide

theorem hardStop_pair_gain_right :
    ∀ v ∈ hardStopRightPair,
      hardStopOldExp v + 1 ≤ hardStopPairPostExp v := by
  intro v hv
  fin_cases v <;> native_decide

theorem hardStop_pair_child_weight_left :
    (∑ v ∈ hardStopLeftPair, 2 ^ hardStopPairPostExp v) ≤ 2 ^ 3 := by
  native_decide

theorem hardStop_pair_child_weight_right :
    (∑ v ∈ hardStopRightPair, 2 ^ hardStopPairPostExp v) ≤ 2 ^ 3 := by
  native_decide

/-- Binary split closes the exact abstract hard-stop profile. -/
theorem hardStop_closed_by_binary_split :
    (∑ v : Fin 4, 2 ^ hardStopOldExp v) ≤ 2 ^ 3 := by
  rcases hardStop_pair_partition with ⟨hdisj, hcover⟩
  exact binary_gain_split_fintype_capacity
    hardStopLeftPair hardStopRightPair
    hardStopOldExp hardStopPairPostExp hardStopPairPostExp
    3 hdisj hcover
    hardStop_pair_gain_left hardStop_pair_gain_right
    hardStop_pair_child_weight_left hardStop_pair_child_weight_right

#print axioms hardStop_closed_by_binary_split

end JSP000404Research
