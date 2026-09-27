import JSP000404Research.ResidualUnsafeSaturatedBlock
import Mathlib.Tactic

/-!
# Unsafe saturated residual pairs in the six-point third-layer profile

An unsafe residual overlap with two exact projected-budget endpoints satisfies

  exponent(u) + exponent(v)
    = n - innerOrientationCredit
    <= n.

Hence any exact-saturated pair whose exponent sum exceeds n cannot be an
unsafe overlap carrier.

For the six-point terminal profile

  top exponent = n-1,
  every other exponent = n-3,

this immediately gives:

* for n>=5, no unsafe exact-saturated top--minimum carrier;
* for n>=7, no unsafe exact-saturated minimum--minimum carrier.

Thus from n>=7 onward every saturated--saturated residual overlap carrier is
forced into the safe-target / flip-displacement branch.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem no_unsafe_saturated_overlap_of_exponent_sum_gt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (hgt : n < exponent u + exponent v) :
    False := by
  have hsum :=
    unsafe_saturated_overlap_exponent_sum_eq_remaining_dimension
      C exponent huWord hvWord hunsafe huSat hvSat
  omega

theorem six_point_profile_no_unsafe_saturated_top_other
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (hn : 5 ≤ n)
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (top : V)
    (hTop : exponent top = n - 1)
    (hMin : ∀ i : V, i ≠ top → exponent i = n - 3)
    {v : V} {word : Fin n → Bool}
    (hvt : v ≠ top)
    (hTopWord : word ∈ retainedCompletionWords C top)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C top v)
    (hTopSat : ExactProjectedBudget C exponent top)
    (hvSat : ExactProjectedBudget C exponent v) :
    False := by
  apply no_unsafe_saturated_overlap_of_exponent_sum_gt
      C exponent hTopWord hvWord hunsafe hTopSat hvSat
  rw [hTop, hMin v hvt]
  omega

theorem six_point_profile_no_unsafe_saturated_other_top
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (hn : 5 ≤ n)
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (top : V)
    (hTop : exponent top = n - 1)
    (hMin : ∀ i : V, i ≠ top → exponent i = n - 3)
    {u : V} {word : Fin n → Bool}
    (hut : u ≠ top)
    (huWord : word ∈ retainedCompletionWords C u)
    (hTopWord : word ∈ retainedCompletionWords C top)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u top)
    (huSat : ExactProjectedBudget C exponent u)
    (hTopSat : ExactProjectedBudget C exponent top) :
    False := by
  apply no_unsafe_saturated_overlap_of_exponent_sum_gt
      C exponent huWord hTopWord hunsafe huSat hTopSat
  rw [hMin u hut, hTop]
  omega

theorem six_point_profile_no_unsafe_saturated_two_minima
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (hn : 7 ≤ n)
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (top : V)
    (hMin : ∀ i : V, i ≠ top → exponent i = n - 3)
    {u v : V} {word : Fin n → Bool}
    (hut : u ≠ top)
    (hvt : v ≠ top)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v) :
    False := by
  apply no_unsafe_saturated_overlap_of_exponent_sum_gt
      C exponent huWord hvWord hunsafe huSat hvSat
  rw [hMin u hut, hMin v hvt]
  omega

#print axioms no_unsafe_saturated_overlap_of_exponent_sum_gt
#print axioms six_point_profile_no_unsafe_saturated_top_other
#print axioms six_point_profile_no_unsafe_saturated_other_top
#print axioms six_point_profile_no_unsafe_saturated_two_minima

end OrderedEdgeColoring
end JSP000404Research
