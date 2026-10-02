import JSP000404Research.ResidualEnlargedLossDegree
import JSP000404Research.WeightedProfileRepair
import Mathlib.Tactic

/-!
# Two leaf outlets collapse to the standard profile alphabet

An EnlargedLeafOutlet remembers the profile type of its leaf:

* strict non-loss, hence positive dyadic projected surplus;
* exact projected budget;
* projected loss.

Therefore two distinct leaf outlets need no further tree recursion at the
top-level reduction. If either leaf is strict we already have paid surplus;
if either is exact we already have an exact-budget outlet; otherwise both
are projected-loss vertices, giving a concrete two-loss pair.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem two_enlargedLeafOutlets_twoLoss_or_paid_or_exact
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    {u v wu wv : V}
    (huT : u ∈ T)
    (hvT : v ∈ T)
    (huv : u ≠ v)
    (hu : EnlargedLeafOutlet C exponent T u wu)
    (hv : EnlargedLeafOutlet C exponent T v wv) :
    (
      u ∈ projectedLossVertices C exponent ∧
      v ∈ projectedLossVertices C exponent
    )
    ∨
    (
      ∃ w : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) w
    )
    ∨
    (
      ∃ w : V,
        ExactProjectedBudget C exponent w
    ) := by
  rcases hu with ⟨huStrict,_huProgress⟩ | ⟨huExact,_huOut⟩ | ⟨huLoss,_huProgress⟩
  · exact Or.inr (Or.inl
      ⟨u, projected_strict_surplus_at_least_one
        exponent (projectedFree C) huStrict⟩)
  · exact Or.inr (Or.inr ⟨u,huExact⟩)
  · rcases hv with ⟨hvStrict,_hvProgress⟩ | ⟨hvExact,_hvOut⟩ | ⟨hvLoss,_hvProgress⟩
    · exact Or.inr (Or.inl
        ⟨v, projected_strict_surplus_at_least_one
          exponent (projectedFree C) hvStrict⟩)
    · exact Or.inr (Or.inr ⟨v,hvExact⟩)
    · exact Or.inl ⟨huLoss,hvLoss⟩

theorem two_enlargedLeafOutlets_standard_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    {u v wu wv : V}
    (huT : u ∈ T)
    (hvT : v ∈ T)
    (huv : u ≠ v)
    (hu : EnlargedLeafOutlet C exponent T u wu)
    (hv : EnlargedLeafOutlet C exponent T v wv) :
    (
      ∃ a b : V,
        a ∈ T ∧ b ∈ T ∧ a ≠ b ∧
        a ∈ projectedLossVertices C exponent ∧
        b ∈ projectedLossVertices C exponent
    )
    ∨
    (
      ∃ w : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) w
    )
    ∨
    (
      ∃ w : V,
        ExactProjectedBudget C exponent w
    ) := by
  rcases
    two_enlargedLeafOutlets_twoLoss_or_paid_or_exact
      C exponent huT hvT huv hu hv
    with hloss | hpaid | hexact
  · exact Or.inl ⟨u,v,huT,hvT,huv,hloss.1,hloss.2⟩
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr hexact)

#print axioms two_enlargedLeafOutlets_twoLoss_or_paid_or_exact
#print axioms two_enlargedLeafOutlets_standard_outlet

end OrderedEdgeColoring
end JSP000404Research
