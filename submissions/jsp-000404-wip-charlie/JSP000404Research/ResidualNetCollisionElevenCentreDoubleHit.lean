import JSP000404Research.ResidualNetCollisionVertexBudgetFibre
import Mathlib.Tactic

/-!
# Exact double-hit accounting for at most eleven original centres

The existing source-native hard-carrier matching theorem proves that
each member of a fixed genuine NET diagonal fibre costs FOUR distinct
original vertices. In configurations with at most eleven vertices this
forces all such fibres to have cardinality at most two.

Consequently the actual diagonal duplicate debt is exactly the number
of distinct diagonals hit by two sources, rather than merely bounded by
a coarse sum of matching capacities. This is a genuine *small-centre*
accounting simplification; it does not turn covered diagonals into true
Boolean holes and does not solve the outstanding global six-source
geometric payment inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A genuine diagonal fibre has at most two sources when the original
configuration has at most eleven vertices. -/
theorem net_collision_fibre_card_le_two_of_centres_le_eleven
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsmall : Fintype.card V ≤ 11)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre
      C exponent hexp honeLoss d).card ≤ 2 := by
  have hfour :=
    net_collision_fibre_four_mul_card_le_vertices
      C exponent hexp honeLoss d
  omega

/-- Distinct diagonal words hit by at least two ACTUAL source words.
This is not a set of Boolean holes: a target may already be covered. -/
noncomputable def netCollisionCertifiedDoubleHitDiagonals
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Finset (Fin n → Bool) :=
  (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).filter
    (fun d => 2 ≤
      (netCollisionCertifiedDiagonalFibre
        C exponent hexp honeLoss d).card)

/-- In the at-most-eleven-centre regime every hit fibre has
cardinality one or two, and EVERY unit of duplicate debt corresponds
to exactly one genuinely double-hit target. No third-source correction
or repeated target multiplicity larger than two can occur. -/
theorem net_collision_duplicate_debt_eq_double_hit_card_of_centres_le_eleven
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsmall : Fintype.card V ≤ 11) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss =
      (netCollisionCertifiedDoubleHitDiagonals
        C exponent hexp honeLoss).card := by
  classical
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  let F := netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss
  change netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss =
    (D.filter (fun d => 2 ≤ (F d).card)).card
  have hpositive (d : Fin n → Bool) (hd : d ∈ D) :
      1 ≤ (F d).card := by
    change d ∈ (Finset.univ : Finset
      {w : Fin n → Bool //
        w ∈ netActualForwardReverseCollisionWords
          C exponent hexp honeLoss}).image
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss) at hd
    obtain ⟨s, _, hsd⟩ := Finset.mem_image.mp hd
    apply Finset.one_le_card.mpr
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsd⟩⟩
  calc
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss =
        ∑ d ∈ D, ((F d).card - 1) :=
      net_collision_certified_duplicate_debt_eq_sum_fibre_excess
        C exponent hexp honeLoss
    _ = ∑ d ∈ D, if 2 ≤ (F d).card then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hpos := hpositive d hd
      have hle :=
        net_collision_fibre_card_le_two_of_centres_le_eleven
          C exponent hexp honeLoss hsmall d
      change (F d).card ≤ 2 at hle
      by_cases htwo : 2 ≤ (F d).card
      · simp [htwo]
        omega
      · simp [htwo]
        omega
    _ = (D.filter (fun d => 2 ≤ (F d).card)).card := by
      simp

/-- An additional exact finite-counting corollary: at most eleven
centres imply the number of extra collision hits cannot exceed the
number of distinct ACTUAL target diagonals. -/
theorem net_collision_duplicate_debt_le_diagonal_image_card_of_centres_le_eleven
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsmall : Fintype.card V ≤ 11) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      (netCollisionCertifiedDiagonalWords
        C exponent hexp honeLoss).card := by
  rw [net_collision_duplicate_debt_eq_double_hit_card_of_centres_le_eleven
    C exponent hexp honeLoss hsmall]
  apply Finset.card_le_card
  exact Finset.filter_subset _ _

#print axioms net_collision_fibre_card_le_two_of_centres_le_eleven
#print axioms net_collision_duplicate_debt_eq_double_hit_card_of_centres_le_eleven
#print axioms net_collision_duplicate_debt_le_diagonal_image_card_of_centres_le_eleven

end OrderedEdgeColoring
end JSP000404Research
