import JSP000404Research.BinaryKraftTree
import Mathlib.Tactic

/-!
# A five-leaf non-comb Kraft extremizer

The lower Sendov capacity is a Kraft inequality, not a unique comb-profile
statement.

Besides Sendov's comb leaf depths, the full binary tree

  node leaf balanced4

has leaf-depth profile

  [1,3,3,3,3].

Thus for every n>=3 the corresponding exponent profile

  [n-1,n-3,n-3,n-3,n-3]

has exact dyadic mass 2^n.

A high-precision exact-normalization five-point search produced precisely this
profile at n=486, delta<1/2.  The geometric realization is not asserted here;
this file formalizes only the exact arithmetic/Kraft fact, which is sufficient
to show that any proof strategy requiring a unique comb extremizer is
unnecessarily strong.
-/

namespace JSP000404Research
namespace BinaryKraftTree

def topLeafBalanced4 : BinaryKraftTree :=
  node leaf balanced4

@[simp] theorem topLeafBalanced4_depths :
    topLeafBalanced4.depths = [1,3,3,3,3] := by
  decide

theorem topLeafBalanced4_kraft_eq
    (n : ℕ) (hn : 3 ≤ n) :
    (topLeafBalanced4.depths.map
      (fun d => 2 ^ (n - d))).sum = 2 ^ n := by
  exact dyadic_depth_sum_eq
    topLeafBalanced4 n (by
      intro d hd
      simp at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> omega)

/-- Explicit exponent-profile form. -/
theorem top_plus_four_third_layer_exact_capacity
    (n : ℕ) (hn : 3 ≤ n) :
    2 ^ (n - 1) +
      2 ^ (n - 3) +
      2 ^ (n - 3) +
      2 ^ (n - 3) +
      2 ^ (n - 3)
      =
    2 ^ n := by
  have h := topLeafBalanced4_kraft_eq n hn
  simpa [topLeafBalanced4_depths] using h

/-- This exact Kraft extremizer violates the comb-style third-tail count:
there are five entries strictly above n-4. -/
theorem top_plus_four_third_layer_tail_not_comb
    (n : ℕ) (hn : 4 ≤ n) :
    (([n - 1, n - 3, n - 3, n - 3, n - 3].filter
      (fun k => n - 4 < k)).length) = 5 := by
  simp
  omega

#print axioms topLeafBalanced4_kraft_eq
#print axioms top_plus_four_third_layer_exact_capacity
#print axioms top_plus_four_third_layer_tail_not_comb

end BinaryKraftTree
end JSP000404Research
