import JSP000404Research.ResidualActiveDrop
import JSP000404Research.ResidualHoleInjection
import JSP000404Research.ResidualSameCodeOrientation
import JSP000404Research.ResidualLightFibreDyadic
import Mathlib.Tactic

/-!
# Exact retained budgets on duplicated retained-code fibres

The residual route does not have a global exact retained-palette bound.  The
available geometric estimate is only the one-layer bound

  card(active(v)) <= n - exponent(v) + 1.

However duplicated retained-code fibres are special.

If u<v have the same retained Boolean code, their joining edge must be the
residual colour.  Hence the residual colour is active at both u and v.
ResidualActiveDrop then removes the extra +1 at both endpoints:

  card(retainedActive(u)) <= n - exponent(u),
  card(retainedActive(v)) <= n - exponent(v).

Therefore every genuinely hard duplicate fibre automatically lies in the
exact-budget regime needed by the heavy/light residual repair lemmas, even
though arbitrary vertices need not.

This is the bridge between one-layer phase loss and the residual fibre
machinery.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A same-retained ordered pair uses the residual colour, hence residual is
active at both endpoints. -/
theorem residual_mem_active_both_of_sameRetained_lt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v) :
    residualCoord n ∈ active C u ∧
      residualCoord n ∈ active C v := by
  have hres := isResidual_of_sameRetained_lt C huv hsame
  exact residualCoord_mem_active_of_isResidual C huv hres

/-- The one-layer active bound upgrades to an exact retained bound at the
lower endpoint of every duplicated retained-code fibre. -/
theorem retainedActive_le_complement_left_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v) :
    (retainedActive C u).card ≤ n - exponent u := by
  exact retainedActive_card_le_of_active_le_add_one_of_residual_mem
    C u (honeLoss u)
    (residual_mem_active_both_of_sameRetained_lt C huv hsame).1

/-- Same exact retained budget at the upper endpoint. -/
theorem retainedActive_le_complement_right_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v) :
    (retainedActive C v).card ≤ n - exponent v := by
  exact retainedActive_card_le_of_active_le_add_one_of_residual_mem
    C v (honeLoss v)
    (residual_mem_active_both_of_sameRetained_lt C huv hsame).2

/-- Pairwise exact-budget package for a duplicated retained-code fibre. -/
theorem sameRetained_exact_pair_budget
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v) :
    (retainedActive C u).card ≤ n - exponent u ∧
      (retainedActive C v).card ≤ n - exponent v := by
  exact ⟨
    retainedActive_le_complement_left_of_sameRetained
      C exponent honeLoss huv hsame,
    retainedActive_le_complement_right_of_sameRetained
      C exponent honeLoss huv hsame⟩

/-- Under the one-layer global bound, a duplicate fibre with no common
inactive coordinate satisfies the strengthened lightness estimate directly. -/
theorem duplicate_exponent_sum_add_commonIncoming_le
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    exponent u + exponent v +
        (incomingRetained C u).card ≤ n := by
  have hpair :=
    sameRetained_exact_pair_budget
      C exponent honeLoss huv hsame
  have hcard :=
    retained_card_sum_ge_n_add_commonIncoming
      C hsame hno
  omega

/-- Direct positive-light-fibre dyadic bound from the one-layer phase budget. -/
theorem duplicate_positive_light_fibre_dyadic_capacity
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
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
    duplicate_exponent_sum_add_commonIncoming_le
      C exponent honeLoss huv hsame hno
  have hsum :
      exponent u + exponent v ≤
        n - (incomingRetained C u).card := by
    omega
  exact two_pow_add_le_two_pow_of_pos_sum_le
    huPos hvPos hsum

#print axioms residual_mem_active_both_of_sameRetained_lt
#print axioms retainedActive_le_complement_left_of_sameRetained
#print axioms retainedActive_le_complement_right_of_sameRetained
#print axioms sameRetained_exact_pair_budget
#print axioms duplicate_exponent_sum_add_commonIncoming_le
#print axioms duplicate_positive_light_fibre_dyadic_capacity

end OrderedEdgeColoring
end JSP000404Research
