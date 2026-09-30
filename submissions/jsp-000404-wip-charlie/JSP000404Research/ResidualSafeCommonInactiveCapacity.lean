import JSP000404Research.ResidualSafeCommonInactiveTensor
import JSP000404Research.ResidualUnsafeSaturatedBlock
import Mathlib.Tactic

/-!
# Dyadic capacity after removing the common free tensor

Let d be the common-inactive dimension of a no-active-safe saturated overlap.
The tensor reduction gives

  (k_u-d) + (k_v-d) + inner = n-d,

where inner = card(in(v)) + card(out(u)).

If both reduced endpoint exponents are positive, the standard two-power
inequality applies in the reduced dimension.  Multiplying back the free tensor
2^d yields

  2^k_u + 2^k_v <= 2^(n-inner).

Thus the positive reduced case has exactly the same ambient Kraft block as the
genuinely unsafe saturated case.  Only reduced-zero endpoints remain terminal.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem noActiveSafe_saturated_positiveReduced_pair_dyadic_capacity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huPos :
      (commonInactiveRetained C u v).card < exponent u)
    (hvPos :
      (commonInactiveRetained C u v).card < exponent v) :
    2 ^ exponent u + 2 ^ exponent v
      ≤
    2 ^
      (n -
        ((incomingRetained C v).card +
         (outgoingRetained C u).card)) := by
  let d := (commonInactiveRetained C u v).card
  let a := exponent u - d
  let b := exponent v - d
  have haPos : 1 ≤ a := by
    dsimp [a,d]
    omega
  have hbPos : 1 ≤ b := by
    dsimp [b,d]
    omega
  have hred :=
    noActiveSafe_saturated_reduced_orientation_identity
      C exponent hno huWord hvWord huSat hvSat
  have hab :
      a + b =
        n - d -
          ((incomingRetained C v).card +
           (outgoingRetained C u).card) := by
    dsimp [a,b,d] at hred ⊢
    omega
  have hpair :
      2 ^ a + 2 ^ b ≤ 2 ^ (a + b) :=
    two_pow_add_le_two_pow_of_pos_sum_le
      haPos hbPos (le_rfl)
  have hdu : d ≤ exponent u := by
    dsimp [d]
    omega
  have hdv : d ≤ exponent v := by
    dsimp [d]
    omega
  have huSplit : d + a = exponent u := by
    dsimp [a]
    omega
  have hvSplit : d + b = exponent v := by
    dsimp [b]
    omega
  have hmul :
      2 ^ d * (2 ^ a + 2 ^ b) ≤
        2 ^ d * 2 ^ (a + b) :=
    Nat.mul_le_mul_left (2 ^ d) hpair
  rw [Nat.mul_add] at hmul
  rw [← pow_add, huSplit, ← pow_add, hvSplit] at hmul
  rw [← pow_add] at hmul
  have hexp :
      d + (a + b) =
        n -
          ((incomingRetained C v).card +
           (outgoingRetained C u).card) := by
    rw [hab]
    have hinner :
        (incomingRetained C v).card +
            (outgoingRetained C u).card ≤ n - d := by
      dsimp [d] at hred
      omega
    omega
  rw [hexp] at hmul
  exact hmul

#print axioms noActiveSafe_saturated_positiveReduced_pair_dyadic_capacity

end OrderedEdgeColoring
end JSP000404Research
