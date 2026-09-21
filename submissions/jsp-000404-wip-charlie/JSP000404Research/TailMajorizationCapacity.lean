import JSP000404Research.PermutedDeficitCapacity
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Tail-majorization outlet for the Sendov dyadic profile

The total target depends only on the multiset of exponents.  A permutation
certificate is therefore still stronger than necessary.

For a finite natural-valued profile f define

  tailCount f r = #{v | r < f(v)}.

Using

  2^a = 1 + sum_{r<a} 2^r,

the total dyadic mass has the layer-cake expansion

  sum_v 2^(f v)
    = |V| + sum_{r<n} 2^r * tailCount f r

whenever f(v) <= n.

Consequently, if profile f has no more entries above every threshold r<n than
profile g, then its total dyadic mass is no larger than that of g.

Applied to an n-colour OrderedEdgeColoring, g(v) is the number of free
coordinates

  n - card(active C v).

Thus the sharp Sendov capacity follows from threshold-count domination alone.
No vertexwise assignment, permutation, or local-palette domination is needed.
This is the weakest profile-level outlet currently used by the project.
-/

namespace JSP000404Research

open scoped BigOperators

def tailCount
    {V : Type*} [Fintype V]
    (f : V → ℕ) (r : ℕ) : ℕ :=
  ((Finset.univ : Finset V).filter fun v => r < f v).card

theorem two_pow_eq_one_add_layers (a : ℕ) :
    2 ^ a = 1 + ∑ r ∈ Finset.range a, 2 ^ r := by
  have h := geom_sum_mul_add (R := ℕ) 1 a
  simpa [Nat.one_add_one_eq_two, Nat.mul_one, add_comm] using h.symm

theorem layers_to_bound
    {a n : ℕ} (ha : a ≤ n) :
    (∑ r ∈ Finset.range n,
        if r < a then 2 ^ r else 0) =
      ∑ r ∈ Finset.range a, 2 ^ r := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext r
    simp
    omega
  · intro r hr
    rfl

theorem sum_indicator_eq_pow_mul_tailCount
    {V : Type*} [Fintype V]
    (f : V → ℕ) (r : ℕ) :
    (∑ v : V, if r < f v then 2 ^ r else 0) =
      2 ^ r * tailCount f r := by
  classical
  unfold tailCount
  rw [← Finset.sum_filter]
  simp [Nat.mul_comm]

theorem dyadic_layer_cake
    {V : Type*} [Fintype V]
    (f : V → ℕ) (n : ℕ)
    (hf : ∀ v, f v ≤ n) :
    (∑ v : V, 2 ^ f v) =
      Fintype.card V +
        ∑ r ∈ Finset.range n, 2 ^ r * tailCount f r := by
  classical
  calc
    (∑ v : V, 2 ^ f v)
        =
      ∑ v : V,
        (1 + ∑ r ∈ Finset.range n,
          if r < f v then 2 ^ r else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [layers_to_bound (hf v)]
        exact two_pow_eq_one_add_layers (f v)
    _ =
      Fintype.card V +
        ∑ v : V, ∑ r ∈ Finset.range n,
          if r < f v then 2 ^ r else 0 := by
        rw [Finset.sum_add_distrib]
        simp
    _ =
      Fintype.card V +
        ∑ r ∈ Finset.range n,
          ∑ v : V, if r < f v then 2 ^ r else 0 := by
        congr 1
        exact Finset.sum_comm
    _ =
      Fintype.card V +
        ∑ r ∈ Finset.range n, 2 ^ r * tailCount f r := by
        apply congrArg (fun x => Fintype.card V + x)
        apply Finset.sum_congr rfl
        intro r hr
        exact sum_indicator_eq_pow_mul_tailCount f r

theorem dyadic_sum_le_of_tailCount_le
    {V : Type*} [Fintype V]
    (f g : V → ℕ) (n : ℕ)
    (hf : ∀ v, f v ≤ n)
    (hg : ∀ v, g v ≤ n)
    (htail :
      ∀ r < n, tailCount f r ≤ tailCount g r) :
    (∑ v : V, 2 ^ f v) ≤
      ∑ v : V, 2 ^ g v := by
  rw [dyadic_layer_cake f n hf, dyadic_layer_cake g n hg]
  gcongr with r hr
  exact htail r (Finset.mem_range.mp hr)

namespace OrderedEdgeColoring

/-- Threshold-count form of the weighted Hansel outlet.

It suffices that for every r<n, the number of target exponents strictly above
r is no greater than the number of vertices leaving strictly more than r free
coordinates in the chosen even partition. -/
theorem exponent_capacity_of_tail_domination
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : OrderedEdgeColoring V n)
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (htail :
      ∀ r < n,
        tailCount exponent r ≤
          tailCount
            (fun v => n - (active C v).card) r) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  have hfree :
      ∀ v, n - (active C v).card ≤ n := by
    intro v
    omega
  have hprofile :=
    dyadic_sum_le_of_tailCount_le
      exponent
      (fun v => n - (active C v).card)
      n hexp hfree htail
  exact hprofile.trans C.weighted_capacity

/-- Equivalent threshold statement written as filtered cardinalities, useful
for geometric counting arguments. -/
theorem exponent_capacity_of_threshold_counts
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (C : OrderedEdgeColoring V n)
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hcount :
      ∀ r < n,
        ((Finset.univ : Finset V).filter
          (fun v => r < exponent v)).card
        ≤
        ((Finset.univ : Finset V).filter
          (fun v => r <
            n - (active C v).card)).card) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  apply exponent_capacity_of_tail_domination C exponent hexp
  intro r hr
  exact hcount r hr

#print axioms exponent_capacity_of_tail_domination
#print axioms exponent_capacity_of_threshold_counts

end OrderedEdgeColoring

#print axioms two_pow_eq_one_add_layers
#print axioms dyadic_layer_cake
#print axioms dyadic_sum_le_of_tailCount_le

end JSP000404Research
