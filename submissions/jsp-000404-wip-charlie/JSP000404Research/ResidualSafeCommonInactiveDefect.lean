import JSP000404Research.ResidualSafeCommonInactiveTensor
import JSP000404Research.ResidualOverlapCube
import Mathlib.Tactic

/-!
# Exact dyadic defect of a reduced-zero safe common-inactive pair

Let
  d = card(commonInactiveRetained C u v).

Under the no-active-safe saturated tensor identity,

  (k_u-d) + (k_v-d) + inner = n-d.

If either reduced endpoint exponent is zero, say k_u=d, then

  n - inner = k_v,

and therefore

  2^k_u + 2^k_v
    = 2^(n-inner) + 2^d.

Thus the entire failure of the positive-reduced pair block is exactly one
common-free tensor atom. Since the overlap cube itself has cardinality 2^d,
the reduced-zero obstruction is precisely the overlap block and nothing more.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem noActiveSafe_reducedZero_left_exact_dyadic_defect
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huZero :
      exponent u = (commonInactiveRetained C u v).card) :
    2 ^ exponent u + 2 ^ exponent v =
      2 ^
        (n -
          ((incomingRetained C v).card +
           (outgoingRetained C u).card))
      +
      2 ^ (commonInactiveRetained C u v).card := by
  have hid :=
    noActiveSafe_saturated_reduced_orientation_identity
      C exponent hno huWord hvWord huSat hvSat
  dsimp at hid
  have hkv :
      exponent v =
        n -
          ((incomingRetained C v).card +
           (outgoingRetained C u).card) := by
    rw [huZero] at hid
    omega
  rw [huZero,hkv]
  omega

theorem noActiveSafe_reducedZero_right_exact_dyadic_defect
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (hvZero :
      exponent v = (commonInactiveRetained C u v).card) :
    2 ^ exponent u + 2 ^ exponent v =
      2 ^
        (n -
          ((incomingRetained C v).card +
           (outgoingRetained C u).card))
      +
      2 ^ (commonInactiveRetained C u v).card := by
  have hid :=
    noActiveSafe_saturated_reduced_orientation_identity
      C exponent hno huWord hvWord huSat hvSat
  dsimp at hid
  have hku :
      exponent u =
        n -
          ((incomingRetained C v).card +
           (outgoingRetained C u).card) := by
    rw [hvZero] at hid
    omega
  rw [hvZero,hku]
  omega

theorem noActiveSafe_reducedZero_defect_eq_overlap_card_left
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huZero :
      exponent u = (commonInactiveRetained C u v).card) :
    2 ^ exponent u + 2 ^ exponent v =
      2 ^
        (n -
          ((incomingRetained C v).card +
           (outgoingRetained C u).card))
      +
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card := by
  rw [retainedCompletionWords_inter_card
      C huWord hvWord]
  exact noActiveSafe_reducedZero_left_exact_dyadic_defect
    C exponent hno huWord hvWord huSat hvSat huZero

theorem noActiveSafe_reducedZero_defect_eq_overlap_card_right
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (hvZero :
      exponent v = (commonInactiveRetained C u v).card) :
    2 ^ exponent u + 2 ^ exponent v =
      2 ^
        (n -
          ((incomingRetained C v).card +
           (outgoingRetained C u).card))
      +
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card := by
  rw [retainedCompletionWords_inter_card
      C huWord hvWord]
  exact noActiveSafe_reducedZero_right_exact_dyadic_defect
    C exponent hno huWord hvWord huSat hvSat hvZero

#print axioms noActiveSafe_reducedZero_left_exact_dyadic_defect
#print axioms noActiveSafe_reducedZero_right_exact_dyadic_defect
#print axioms noActiveSafe_reducedZero_defect_eq_overlap_card_left
#print axioms noActiveSafe_reducedZero_defect_eq_overlap_card_right

end OrderedEdgeColoring
end JSP000404Research
