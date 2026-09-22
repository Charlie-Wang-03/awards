
import JSP000404Research.ResidualDuplicateBudget
import JSP000404Research.ResidualLists
import JSP000404Research.ResidualLightFibreDyadic
import Mathlib.Tactic

/-!
# Strengthened budget on a residual edge with no safe retained colour

For a residual increasing edge u<v define the exact local forbidden list

  incomingRetained(u) union outgoingRetained(v).

If this list is the whole retained palette Fin n, then there is no canonical
safe target colour for ordinary residual recolouring.

Let

  J(u,v) = incomingRetained(u) inter outgoingRetained(v).

The union/intersection cardinality identity gives

  n + card J
    = card incoming(u) + card outgoing(v).

Under the global one-layer active bound, a residual edge makes the residual
colour active at both endpoints, so both retained palettes satisfy the exact
projected budgets

  card retainedActive(u) <= n-exponent(u),
  card retainedActive(v) <= n-exponent(v).

Since incoming(u) and outgoing(v) are contained in the corresponding retained
active palettes, every unsafe residual edge satisfies

  exponent(u) + exponent(v) + card J(u,v) <= n.

For positive endpoint exponents this yields the dyadic pair bound

  2^ku + 2^kv <= 2^(n-card J).

The extra intersection term is geometric information: every c in J is
realized by a same-band edge entering u and another same-band edge leaving v.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def residualThroughColours
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) : Finset (Fin n) :=
  incomingRetained C u ∩ outgoingRetained C v

@[simp] theorem mem_residualThroughColours
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) :
    c ∈ residualThroughColours C u v ↔
      c ∈ incomingRetained C u ∧
      c ∈ outgoingRetained C v := by
  classical
  simp [residualThroughColours]

theorem incomingRetained_subset_retainedActive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    incomingRetained C v ⊆ retainedActive C v := by
  intro c hc
  rw [retainedActive_eq_incoming_union_outgoing C v]
  exact Finset.mem_union_left _ hc

theorem outgoingRetained_subset_retainedActive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    outgoingRetained C v ⊆ retainedActive C v := by
  intro c hc
  rw [retainedActive_eq_incoming_union_outgoing C v]
  exact Finset.mem_union_right _ hc

/-- Exact set identity for an unsafe residual edge. -/
theorem unsafe_residual_union_eq_univ
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    incomingRetained C u ∪ outgoingRetained C v =
      (Finset.univ : Finset (Fin n)) := by
  classical
  apply Finset.eq_univ_of_forall
  intro c
  by_contra hc
  apply hunsafe
  refine ⟨c, ?_⟩
  simpa [residualForbidden] using hc

/-- Union/intersection accounting for an unsafe residual edge. -/
theorem unsafe_residual_card_balance
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    n + (residualThroughColours C u v).card =
      (incomingRetained C u).card +
        (outgoingRetained C v).card := by
  classical
  have hcard :=
    Finset.card_union_add_card_inter
      (incomingRetained C u)
      (outgoingRetained C v)
  rw [unsafe_residual_union_eq_univ C hunsafe] at hcard
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  simpa [residualThroughColours, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc] using hcard

/-- Main strengthened lightness inequality. -/
theorem unsafe_residual_exponent_sum_add_through_le
    {V : Type*} [LinearOrder V] {n : ℕ}
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
        (residualThroughColours C u v).card ≤ n := by
  have hresActive :=
    residualCoord_mem_active_of_isResidual C huv hres
  have hretU :
      (retainedActive C u).card ≤ n - exponent u :=
    retainedActive_card_le_of_active_le_add_one_of_residual_mem
      C u (honeLoss u) hresActive.1
  have hretV :
      (retainedActive C v).card ≤ n - exponent v :=
    retainedActive_card_le_of_active_le_add_one_of_residual_mem
      C v (honeLoss v) hresActive.2
  have hinc :
      (incomingRetained C u).card ≤
        (retainedActive C u).card :=
    Finset.card_le_card
      (incomingRetained_subset_retainedActive C u)
  have hout :
      (outgoingRetained C v).card ≤
        (retainedActive C v).card :=
    Finset.card_le_card
      (outgoingRetained_subset_retainedActive C v)
  have hbal :=
    unsafe_residual_card_balance C hunsafe
  have huN := hexp u
  have hvN := hexp v
  omega

/-- Positive unsafe residual pairs fit dyadically inside the block obtained by
fixing the through-colour pattern. -/
theorem unsafe_residual_positive_pair_dyadic_capacity
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huPos : 1 ≤ exponent u)
    (hvPos : 1 ≤ exponent v) :
    2 ^ exponent u + 2 ^ exponent v ≤
      2 ^ (n - (residualThroughColours C u v).card) := by
  have hsum :=
    unsafe_residual_exponent_sum_add_through_le
      C exponent hexp honeLoss huv hres hunsafe
  have hpair :
      exponent u + exponent v ≤
        n - (residualThroughColours C u v).card := by
    omega
  exact two_pow_add_le_two_pow_of_pos_sum_le
    huPos hvPos hpair

/-- Every through colour has explicit witnesses on both sides of the residual
edge. -/
theorem throughColour_has_outer_witnesses
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c : Fin n}
    (hc : c ∈ residualThroughColours C u v) :
    (∃ a, a < u ∧ C.color a u = c.castSucc) ∧
    (∃ w, v < w ∧ C.color v w = c.castSucc) := by
  have hc' := (mem_residualThroughColours C u v c).1 hc
  constructor
  · exact (mem_incomingRetained_iff C u c).1 hc'.1
  · exact (mem_outgoingRetained_iff C v c).1 hc'.2

#print axioms unsafe_residual_card_balance
#print axioms unsafe_residual_exponent_sum_add_through_le
#print axioms unsafe_residual_positive_pair_dyadic_capacity
#print axioms throughColour_has_outer_witnesses

end OrderedEdgeColoring
end JSP000404Research
