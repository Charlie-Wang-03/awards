import JSP000404Research.ResidualHoleInjection
import JSP000404Research.ResidualCommonInactive
import Mathlib.Tactic

/-!
# High-exponent residual duplicates have a certified Boolean hole

Work with an OrderedEdgeColoring by n+1 colours and retain the first n
coordinates.  Suppose the retained active-colour count at every vertex v is
bounded by the Sendov deficit

  n - exponent(v).

If two distinct vertices u,v have the same retained code and

  exponent(u) + exponent(v) > n,

then their two deficits have sum strictly below n.  ResidualCommonInactive
therefore supplies a retained coordinate which is inactive at both endpoints.
ResidualHoleInjection then shows that flipping that coordinate in their common
retained code lands in a Boolean word which is not used by any original
vertex.

Thus every "heavy" duplicated retained-code fibre has an explicit globally
free neighbouring code.  The unresolved weighted residual problem is confined
to duplicate pairs satisfying exponent(u)+exponent(v) <= n.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_common_inactive_of_exponent_sum_gt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hret :
      ∀ v,
        (retainedActive C v).card ≤ n - exponent v)
    {u v : V}
    (hsum : n < exponent u + exponent v) :
    ∃ c : Fin n,
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v := by
  have hdef :
      (n - exponent u) + (n - exponent v) < n := by
    have hu := hexp u
    have hv := hexp v
    omega
  exact exists_common_inactive_of_deficit_sum_lt
    C (hret u) (hret v) hdef

/-- Heavy duplicated retained codes admit a one-coordinate repair into an
unoccupied Boolean word. -/
theorem heavy_sameRetained_has_free_neighbour
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hret :
      ∀ v,
        (retainedActive C v).card ≤ n - exponent v)
    {u v : V}
    (huv : u ≠ v)
    (hsame : SameRetained C u v)
    (hsum : n < exponent u + exponent v) :
    ∃ c : Fin n,
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v ∧
      ¬ ∃ w : V,
        (fun d => retainedBit C w d) =
          flippedRetainedCode C u c := by
  obtain ⟨c, hcu, hcv⟩ :=
    exists_common_inactive_of_exponent_sum_gt
      C exponent hexp hret hsum
  refine ⟨c, hcu, hcv, ?_⟩
  exact no_vertex_retainedCode_eq_flipped_common_inactive
    C c huv hsame hcu hcv

/-- Ordered form for a hard residual duplicate pair.  SameRetained already
forces the joining edge to be residual. -/
theorem heavy_sameRetained_lt_has_residual_hole
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hret :
      ∀ v,
        (retainedActive C v).card ≤ n - exponent v)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hsum : n < exponent u + exponent v) :
    IsResidual C u v ∧
      ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v ∧
        ¬ ∃ w : V,
          (fun d => retainedBit C w d) =
            flippedRetainedCode C u c := by
  constructor
  · exact isResidual_of_sameRetained_lt C huv hsame
  · exact heavy_sameRetained_has_free_neighbour
      C exponent hexp hret (ne_of_lt huv) hsame hsum

#print axioms exists_common_inactive_of_exponent_sum_gt
#print axioms heavy_sameRetained_has_free_neighbour
#print axioms heavy_sameRetained_lt_has_residual_hole

end OrderedEdgeColoring
end JSP000404Research
