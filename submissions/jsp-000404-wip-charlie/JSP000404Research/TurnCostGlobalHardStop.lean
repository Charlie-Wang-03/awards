
import JSP000404Research.AlternativeKraftExtremizer
import JSP000404Research.DyadicTurnCost
import Mathlib.Tactic

/-!
# Hard stop for a global per-centre turn-cost proof

DyadicTurnCost is a powerful local outlet:

  if cost(i) >= exponent(i)+1
  and sum cost(i) <= 2*n,

then the Sendov dyadic capacity follows.

It cannot, however, be the universal global mechanism.

The valid five-leaf Kraft extremizer

  [n-1, n-3, n-3, n-3, n-3]

has exact dyadic mass 2^n, but its mandatory pointwise lower cost
sum(exponent+1) is

  n + 4*(n-2) = 5*n-8,

which is strictly larger than 2*n for every n>=3.

Thus any global proof must allow binary/Kraft reuse of one unit of geometric
credit across descendants; it cannot assign an independent turn budget k+1 to
every centre.
-/

namespace JSP000404Research

def alternativeKraftExponent5 (n : ℕ) : Fin 5 → ℕ :=
  ![n - 1, n - 3, n - 3, n - 3, n - 3]

theorem alternativeKraftExponent5_mass
    (n : ℕ) (hn : 3 ≤ n) :
    (∑ i : Fin 5, 2 ^ alternativeKraftExponent5 n i) = 2 ^ n := by
  simpa [alternativeKraftExponent5, Fin.sum_univ_succ]
    using
      BinaryKraftTree.top_plus_four_third_layer_exact_capacity
        n hn

theorem alternativeKraftExponent5_mandatory_cost_sum
    (n : ℕ) (hn : 3 ≤ n) :
    (∑ i : Fin 5, (alternativeKraftExponent5 n i + 1))
      = 5 * n - 8 := by
  simp [alternativeKraftExponent5, Fin.sum_univ_succ]
  omega

theorem alternativeKraftExponent5_cost_gt_two_n
    (n : ℕ) (hn : 3 ≤ n) :
    2 * n <
      ∑ i : Fin 5, (alternativeKraftExponent5 n i + 1) := by
  rw [alternativeKraftExponent5_mandatory_cost_sum n hn]
  omega

/-- No cost assignment dominating exponent+1 can have total at most 2*n on
this exact Kraft extremizer. -/
theorem no_global_turn_cost_certificate_on_alternative_extremizer
    (n : ℕ) (hn : 3 ≤ n) :
    ¬ ∃ cost : Fin 5 → ℕ,
      (∀ i, alternativeKraftExponent5 n i + 1 ≤ cost i) ∧
      (∑ i, cost i) ≤ 2 * n := by
  rintro ⟨cost, hdom, hsum⟩
  have hlower :
      (∑ i : Fin 5, (alternativeKraftExponent5 n i + 1))
        ≤ ∑ i : Fin 5, cost i :=
    Finset.sum_le_sum fun i _ => hdom i
  have hgt :=
    alternativeKraftExponent5_cost_gt_two_n n hn
  omega

#print axioms alternativeKraftExponent5_mass
#print axioms alternativeKraftExponent5_mandatory_cost_sum
#print axioms alternativeKraftExponent5_cost_gt_two_n
#print axioms no_global_turn_cost_certificate_on_alternative_extremizer

end JSP000404Research
