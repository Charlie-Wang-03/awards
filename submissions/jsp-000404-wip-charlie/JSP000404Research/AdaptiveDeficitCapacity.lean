import JSP000404Research.AdaptiveDirectionColor
import Mathlib.Tactic

/-!
# Adaptive-colouring capacity from local deficit palettes

A full KraftCertificate is stronger than necessary.

Suppose an n-colour adaptive direction colouring is available and the number
of colours incident to each centre v is at most its Sendov deficit ell(v).
The weighted Hansel inequality for the adaptive colouring gives

  sum_v 2^(n-active(v)) <= 2^n.

Since active(v) <= ell(v), every target cluster weight

  2^(n-ell(v))

is no larger than the corresponding Hansel term.  Thus

  sum_v 2^(n-ell(v)) <= 2^n.

If ell(v)=n-exponent(v), this is exactly

  sum_v 2^exponent(v) <= 2^n.

This is the weakest clean global outlet currently known.  Geometry no longer
needs to construct exact partial Boolean words; it only needs one global
adaptive edge-colouring whose local palettes are bounded by the centre
deficits.
-/

namespace JSP000404Research
namespace DirectionData
namespace AdaptiveColoring

open scoped BigOperators

/-- Local active-palette bounds by deficits imply the weighted deficit
capacity directly. -/
theorem deficit_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {n : ℕ}
    {D : DirectionData V width}
    (C : AdaptiveColoring D n)
    (ell : V → ℕ)
    (hactive :
      ∀ v,
        (OrderedEdgeColoring.active
          C.toOrderedEdgeColoring v).card ≤ ell v) :
    (∑ v, 2 ^ (n - ell v)) ≤ 2 ^ n := by
  have hweighted := C.weighted_capacity
  calc
    (∑ v, 2 ^ (n - ell v))
        ≤ ∑ v, 2 ^ (n -
            (OrderedEdgeColoring.active
              C.toOrderedEdgeColoring v).card) := by
          apply Finset.sum_le_sum
          intro v _
          apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
          omega
    _ ≤ 2 ^ n := hweighted

/-- Exponent form of the same theorem. -/
theorem exponent_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {n : ℕ}
    {D : DirectionData V width}
    (C : AdaptiveColoring D n)
    (exponent ell : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hell : ∀ v, ell v = n - exponent v)
    (hactive :
      ∀ v,
        (OrderedEdgeColoring.active
          C.toOrderedEdgeColoring v).card ≤ ell v) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  have h := deficit_capacity C ell hactive
  calc
    (∑ v, 2 ^ exponent v)
        = ∑ v, 2 ^ (n - ell v) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [hell v]
          rw [Nat.sub_sub_cancel (hexp v)]
    _ ≤ 2 ^ n := h

/-- A directly usable form when the local palette bound is stated as
n-exponent(v). -/
theorem exponent_capacity_of_active_le_complement
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {n : ℕ}
    {D : DirectionData V width}
    (C : AdaptiveColoring D n)
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hactive :
      ∀ v,
        (OrderedEdgeColoring.active
          C.toOrderedEdgeColoring v).card ≤
          n - exponent v) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  exact exponent_capacity
    C exponent (fun v => n - exponent v)
    hexp (fun _ => rfl) hactive

#print axioms deficit_capacity
#print axioms exponent_capacity
#print axioms exponent_capacity_of_active_le_complement

end AdaptiveColoring
end DirectionData
end JSP000404Research
