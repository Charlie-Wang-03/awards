import JSP000404Research.ActualOneHighLossCentreFibrePacking
import JSP000404Research.ActualAnyWidthGlobalOppositeDebtPacking
import Mathlib.Tactic

/-!
# Original global loss-duplicate debt with ONE high exponent centre

For arbitrary width n and arbitrary loss exponent profile, if at most
one actual original projected-loss centre has exponent >=3, every
source fibre of an actual opposite Boolean candidate injects into the
ACTUAL low-exponent (<=2) projected-loss vertices.

Unlike the previous 2 Ddup <= |L| |O|, this theorem does NOT assume
exponent <=2 for all centres. It yields the ORIGINAL debt bound
 Ddup <= |actual low-loss centres| * |actual opposite candidates|.

No candidate is claimed to be a true exterior hole or spare surplus.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Exact global REAL loss-debt capacity for mixed high/low profiles:
at most one high original projected-loss centre limits every opposite
fibre to the count of actual low original projected-loss centres. -/
theorem actual_one_high_loss_centre_global_duplicate_debt_le_low_mul_candidates
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hhigh :
      ((projectedLossVertices C exponent).filter
        (fun v => 3 ≤ exponent v)).card ≤ 1) :
    translatedLossDuplicateDebt C exponent choice ≤
      ((projectedLossVertices C exponent).filter
        (fun v => exponent v ≤ 2)).card *
      (actualLossEarliestOppositeCandidateWords C exponent choice).card := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  let O := actualLossEarliestOppositeCandidateWords C exponent choice
  let Low := (projectedLossVertices C exponent).filter
    (fun v => exponent v ≤ 2)
  let f : (Fin n × Fin n × (Fin n → Bool)) → (Fin n → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  have hsum :
      S.card = ∑ q ∈ O, (S.filter (fun a => f a = q)).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hper (q : Fin n → Bool) :
      (S.filter (fun a => f a = q)).card ≤ Low.card := by
    exact actual_one_high_loss_centre_opposite_fibre_le_low_centres
      C exponent choice hhigh q
  have htotal :
      (∑ q ∈ O, (S.filter (fun a => f a = q)).card) ≤
        ∑ q ∈ O, Low.card :=
    Finset.sum_le_sum (fun q hq => hper q)
  calc
    translatedLossDuplicateDebt C exponent choice = S.card :=
      (actual_earliest_collision_records_card_eq_duplicate_debt
        C exponent choice).symm
    _ = ∑ q ∈ O, (S.filter (fun a => f a = q)).card := hsum
    _ ≤ ∑ q ∈ O, Low.card := htotal
    _ = Low.card * O.card := by simp [mul_comm]

#print axioms actual_one_high_loss_centre_global_duplicate_debt_le_low_mul_candidates

end OrderedEdgeColoring
end JSP000404Research
