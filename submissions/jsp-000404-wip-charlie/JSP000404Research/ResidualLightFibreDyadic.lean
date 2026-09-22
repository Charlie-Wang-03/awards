import JSP000404Research.ResidualSameCodeOrientation
import Mathlib.Tactic

/-!
# Dyadic capacity of positive light residual fibres

Suppose a duplicated retained-code fibre has two positive exponents a,b and
cannot be repaired by a common inactive coordinate.

ResidualSameCodeOrientation gives the strengthened lightness inequality

  a + b + i <= n,

where i is the number of common incoming retained colours.  Since a,b>=1,

  2^a + 2^b <= 2^(a+b) <= 2^(n-i).

Thus the entire positive duplicated fibre fits inside the Boolean upper cube
obtained by fixing its common incoming bits.

This closes the internal dyadic accounting of every positive light fibre.
The remaining global issue is packing these per-fibre upper-cube capacities
across distinct incoming patterns.
-/

namespace JSP000404Research

/-- Two positive dyadic masses whose exponents sum to at most N fit inside one
N-dimensional dyadic block. -/
theorem two_pow_add_le_two_pow_of_pos_sum_le
    {a b N : ℕ}
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hsum : a + b ≤ N) :
    2 ^ a + 2 ^ b ≤ 2 ^ N := by
  have hN : 2 ≤ N := by omega
  have haTop : a ≤ N - 1 := by omega
  have hbTop : b ≤ N - 1 := by omega
  have hpa :
      2 ^ a ≤ 2 ^ (N - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) haTop
  have hpb :
      2 ^ b ≤ 2 ^ (N - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hbTop
  have hsumPow :
      2 ^ a + 2 ^ b ≤
        2 ^ (N - 1) + 2 ^ (N - 1) :=
    Nat.add_le_add hpa hpb
  have htop :
      2 ^ (N - 1) + 2 ^ (N - 1) = 2 ^ N := by
    have hsub : N - 1 + 1 = N := by omega
    calc
      2 ^ (N - 1) + 2 ^ (N - 1)
          = 2 * 2 ^ (N - 1) := by ring
      _ = 2 ^ (N - 1) * 2 := by ring
      _ = 2 ^ N := by rw [← pow_succ, hsub]
  exact hsumPow.trans_eq htop

namespace OrderedEdgeColoring

/-- Positive same-retained fibres with no common inactive coordinate fit
dyadically inside the block left after fixing their common incoming colours. -/
theorem positive_light_fibre_dyadic_capacity
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hret :
      ∀ x,
        (retainedActive C x).card ≤ n - exponent x)
    {u v : V}
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v)
    (huPos : 1 ≤ exponent u)
    (hvPos : 1 ≤ exponent v) :
    2 ^ exponent u + 2 ^ exponent v ≤
      2 ^ (n - (incomingRetained C u).card) := by
  have hlight :=
    exponent_sum_add_commonIncoming_le_of_no_common_inactive
      C exponent hret hsame hno
  have hsum :
      exponent u + exponent v ≤
        n - (incomingRetained C u).card := by
    omega
  exact two_pow_add_le_two_pow_of_pos_sum_le
    huPos hvPos hsum

/-- The extremal equality regime forces the whole strengthened lightness
budget to be saturated.  This is useful when classifying fibres which consume
their complete incoming-pattern block. -/
theorem positive_light_fibre_eq_top_forces_sum_eq
    {a b N : ℕ}
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hsum : a + b ≤ N)
    (heq : 2 ^ a + 2 ^ b = 2 ^ N) :
    a + b = N := by
  by_contra hne
  have hlt : a + b < N := by omega
  have hsmall :
      2 ^ (a + b) ≤ 2 ^ (N - 1) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have hpair :
      2 ^ a + 2 ^ b ≤ 2 ^ (a + b) :=
    two_pow_add_le_two_pow_of_pos_sum_le ha hb le_rfl
  have htoplt : 2 ^ (N - 1) < 2 ^ N := by
    exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
  rw [heq] at hpair
  exact (not_lt_of_ge (hpair.trans hsmall)) htoplt

#print axioms two_pow_add_le_two_pow_of_pos_sum_le
#print axioms positive_light_fibre_dyadic_capacity
#print axioms positive_light_fibre_eq_top_forces_sum_eq

end OrderedEdgeColoring
end JSP000404Research
