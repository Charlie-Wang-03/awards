import JSP000404Research.ResidualFreeNeighbour
import Mathlib.Tactic

/-!
# Low combined retained activity gives a common inactive coordinate

For two vertices in an n-colour retained system, if the sum of their retained
active-colour counts is strictly below n, then the union of those active sets
cannot fill all retained coordinates.  Hence there is a colour inactive at
both endpoints.

For a hard residual vertical pair this supplies the hypothesis of
ResidualFreeNeighbour and therefore an unoccupied adjacent Boolean code.

In Sendov deficit language, any local bounds

  card(retainedActive u) <= ell_u,
  card(retainedActive v) <= ell_v,
  ell_u + ell_v < n

are sufficient.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Two small subsets of Fin n have a common missing coordinate. -/
theorem exists_common_not_mem_of_card_add_lt
    {n : ℕ}
    (A B : Finset (Fin n))
    (hcard : A.card + B.card < n) :
    ∃ c : Fin n, c ∉ A ∧ c ∉ B := by
  classical
  have hunion :
      (A ∪ B).card < n := by
    have hle : (A ∪ B).card ≤ A.card + B.card :=
      Finset.card_union_le A B
    omega
  obtain ⟨c, hc⟩ :=
    exists_fin_not_mem_of_card_lt (A ∪ B) hunion
  rw [Finset.mem_union] at hc
  push_neg at hc
  exact ⟨c, hc.1, hc.2⟩

/-- Retained-active count criterion for a common inactive colour. -/
theorem exists_common_inactive_of_retained_card_add_lt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hcard :
      (retainedActive C u).card +
        (retainedActive C v).card < n) :
    ∃ c : Fin n,
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v := by
  exact exists_common_not_mem_of_card_add_lt
    (retainedActive C u) (retainedActive C v) hcard

/-- Prescribed local deficit bounds imply a common inactive retained colour. -/
theorem exists_common_inactive_of_deficit_sum_lt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {ellU ellV : ℕ}
    (hu : (retainedActive C u).card ≤ ellU)
    (hv : (retainedActive C v).card ≤ ellV)
    (hell : ellU + ellV < n) :
    ∃ c : Fin n,
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v := by
  apply exists_common_inactive_of_retained_card_add_lt C
  omega

/-- A vertical pair whose two retained-active budgets sum to less than n has
at least one locally free neighbouring retained code. -/
theorem hard_pair_has_free_neighbour_of_deficit_sum_lt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u ≠ v)
    (hret : ∀ d : Fin n,
      retainedBit C u d = retainedBit C v d)
    {ellU ellV : ℕ}
    (hu : (retainedActive C u).card ≤ ellU)
    (hv : (retainedActive C v).card ≤ ellV)
    (hell : ellU + ellV < n) :
    ∃ c : Fin n,
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v ∧
      ¬ ∃ w : V,
        retainedBit C w c ≠ retainedBit C u c ∧
        (∀ d : Fin n, d ≠ c →
          retainedBit C w d = retainedBit C u d) := by
  obtain ⟨c, hcu, hcv⟩ :=
    exists_common_inactive_of_deficit_sum_lt
      C hu hv hell
  refine ⟨c, hcu, hcv, ?_⟩
  exact no_vertex_realizes_flipped_common_inactive_code
    C c huv hret
    (by simpa [retainedActive] using hcu)
    (by simpa [retainedActive] using hcv)

#print axioms exists_common_not_mem_of_card_add_lt
#print axioms exists_common_inactive_of_retained_card_add_lt
#print axioms exists_common_inactive_of_deficit_sum_lt
#print axioms hard_pair_has_free_neighbour_of_deficit_sum_lt

end OrderedEdgeColoring
end JSP000404Research
