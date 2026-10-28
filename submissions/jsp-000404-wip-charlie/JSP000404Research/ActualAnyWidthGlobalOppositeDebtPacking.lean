import JSP000404Research.ActualAnyWidthOppositeFibrePacking
import Mathlib.Tactic

/-!
# All-n GLOBAL original collision debt bound from REAL centre packing

Each genuine opposite-candidate fibre q uses at least twice as many
distinct actual projected-loss centres as its number of debt records.
Summing only over the ACTUAL opposite candidates yields

  2 * translatedLossDuplicateDebt <=
    |projectedLossVertices| * |actualLossEarliestOppositeCandidateWords|.

This is an unconditional global source-counting consequence of the
dimension-free true-source local packing (under exponent<=2). It is
not a proof that opposite candidates are TRUE exterior holes and it
does not spend unused dyadic surplus.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Global source-native eighth-debt multiplicity cannot exceed
half the number of REAL projected-loss centres times the number
of distinct ACTUAL opposite-corner candidates. The bound is valid
in any Boolean dimension and directly controls ORIGINAL debt tokens.
It creates no hole eligibility or spending credit. -/
theorem actual_any_width_global_duplicate_debt_twice_le_centres_mul_candidates
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hexp : ∀ v, exponent v ≤ 2) :
    2 * translatedLossDuplicateDebt C exponent choice ≤
      (projectedLossVertices C exponent).card *
        (actualLossEarliestOppositeCandidateWords C exponent choice).card := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  let O := actualLossEarliestOppositeCandidateWords C exponent choice
  let L := projectedLossVertices C exponent
  let f : (Fin n × Fin n × (Fin n → Bool)) → (Fin n → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  have hsum :
      S.card = ∑ q ∈ O, (S.filter (fun a => f a = q)).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hper (q : Fin n → Bool) :
      2 * (S.filter (fun a => f a = q)).card ≤ L.card := by
    exact actual_any_width_opposite_fibre_twice_card_le_loss_centres
      C exponent choice hexp q
  have htotal :
      (∑ q ∈ O, 2 * (S.filter (fun a => f a = q)).card) ≤
        ∑ q ∈ O, L.card :=
    Finset.sum_le_sum (fun q hq => hper q)
  calc
    2 * translatedLossDuplicateDebt C exponent choice =
        2 * S.card := by
          rw [actual_earliest_collision_records_card_eq_duplicate_debt
            C exponent choice]
    _ = 2 * (∑ q ∈ O, (S.filter (fun a => f a = q)).card) := by
      rw [hsum]
    _ = ∑ q ∈ O, 2 * (S.filter (fun a => f a = q)).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ O, L.card := htotal
    _ = L.card * O.card := by simp [mul_comm]

/-- A sharpened maximum source multiplicity bound, simultaneously
including the strict original coordinate-pair count and the number
of original loss centres. Neither right-hand budget is a true hole. -/
theorem actual_any_width_opposite_fibre_two_independent_capacities
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hexp : ∀ v, exponent v ≤ 2)
    (q : Fin n → Bool) :
    (actualLossOppositeCandidateFibre C exponent choice q).card ≤
        (actualLossOrderedCoordinatePairs n).card ∧
      2 * (actualLossOppositeCandidateFibre C exponent choice q).card ≤
        (projectedLossVertices C exponent).card := by
  exact ⟨actual_loss_opposite_fibre_card_le_ordered_pairs
    C exponent choice q,
    actual_any_width_opposite_fibre_twice_card_le_loss_centres
      C exponent choice hexp q⟩

#print axioms actual_any_width_global_duplicate_debt_twice_le_centres_mul_candidates
#print axioms actual_any_width_opposite_fibre_two_independent_capacities

end OrderedEdgeColoring
end JSP000404Research
