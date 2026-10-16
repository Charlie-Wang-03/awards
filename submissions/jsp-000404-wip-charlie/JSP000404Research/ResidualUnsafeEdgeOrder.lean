
import JSP000404Research.ResidualThroughDensity
import Mathlib.Tactic

/-!
# Unsafe residual edges consume vertices on both sides

For c in the through-colour set

  J(u,v) = incomingRetained(u) inter outgoingRetained(v),

there is an edge a--u of colour c with a<u and an edge v--w of colour c with
v<w.

Distinct colours force distinct witnesses, since a fixed edge has only one
colour.  Therefore J(u,v) injects into the strict-left vertices of u and into
the strict-right vertices of v.

Combined with the strengthened unsafe-edge budget

  exponent(u)+exponent(v)+card J(u,v) <= n,

this ties the local dyadic weight of an unsafe residual edge to actual room on
both sides in the ambient linear order.

At an extreme endpoint this becomes rigid: if u has no vertices to its left,
then J is empty and unsafety forces every retained colour to be outgoing at v.
Because the residual colour is also active at v, v uses all n+1 colours; under
the standard one-layer active bound this forces exponent(v)=0.  The symmetric
statement holds at a rightmost endpoint.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Through colours inject into actual vertices strictly left of u. -/
theorem throughColours_card_le_strictLeft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (residualThroughColours C u v).card ≤
      (strictLeftVertices u).card := by
  exact residualThroughColours_card_le_left C u v

/-- Through colours inject into actual vertices strictly right of v. -/
theorem throughColours_card_le_strictRight
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (residualThroughColours C u v).card ≤
      (strictRightVertices v).card := by
  exact residualThroughColours_card_le_right C u v

/-- Unsafe residual edge: exponent sum plus available left/right order room is
bounded through the same through-colour credit. -/
theorem unsafe_residual_exponent_sum_add_min_side_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    exponent u + exponent v +
        (residualThroughColours C u v).card ≤ n ∧
    (residualThroughColours C u v).card ≤
        (strictLeftVertices u).card ∧
    (residualThroughColours C u v).card ≤
        (strictRightVertices v).card := by
  exact ⟨
    unsafe_residual_exponent_sum_add_through_le
      C exponent hexp honeLoss huv hres hunsafe,
    throughColours_card_le_strictLeft C u v,
    throughColours_card_le_strictRight C u v⟩

/-- If the lower endpoint has no vertex to its left, an unsafe residual edge
forces the upper endpoint to have exponent zero. -/
theorem unsafe_residual_from_leftmost_forces_upper_exponent_zero
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (hleft : (strictLeftVertices u).card = 0)
    (huv : u < v)
    (hres : IsResidual C u v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    exponent v = 0 := by
  have hnone : ∀ a : V, ¬ a < u := by
    intro a ha
    have hmem : a ∈ strictLeftVertices u :=
      (mem_strictLeftVertices u a).2 ha
    have hpositive : 0 < (strictLeftVertices u).card :=
      Finset.card_pos.mpr ⟨a, hmem⟩
    omega
  exact exponent_upper_eq_zero_of_unsafe_residual_from_no_left
    C exponent hexp honeLoss huv hres hunsafe hnone

/-- Symmetric rightmost form. -/
theorem unsafe_residual_to_rightmost_forces_lower_exponent_zero
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (hright : (strictRightVertices v).card = 0)
    (huv : u < v)
    (hres : IsResidual C u v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    exponent u = 0 := by
  have hnone : ∀ w : V, ¬ v < w := by
    intro w hvw
    have hmem : w ∈ strictRightVertices v :=
      (mem_strictRightVertices v w).2 hvw
    have hpositive : 0 < (strictRightVertices v).card :=
      Finset.card_pos.mpr ⟨w, hmem⟩
    omega
  exact exponent_lower_eq_zero_of_unsafe_residual_to_no_right
    C exponent hexp honeLoss huv hres hunsafe hnone

#print axioms throughColours_card_le_strictLeft
#print axioms throughColours_card_le_strictRight
#print axioms unsafe_residual_exponent_sum_add_min_side_le
#print axioms unsafe_residual_from_leftmost_forces_upper_exponent_zero
#print axioms unsafe_residual_to_rightmost_forces_lower_exponent_zero

end OrderedEdgeColoring
end JSP000404Research
