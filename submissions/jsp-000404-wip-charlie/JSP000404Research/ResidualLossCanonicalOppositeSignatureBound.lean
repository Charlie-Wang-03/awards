import JSP000404Research.ResidualLossCanonicalOppositePairRigidity
import JSP000404Research.ResidualLossGlobalNonlocalShortfallLedger
import Mathlib.Tactic

/-!
# Source-native injection: actual collision debt into opposite candidate × original coordinate pair

This proves a universal and quantitative rigidity principle that does not
need any exterior-hole eligibility or AngleCap assumptions. Every true
earliest-prior loss debt record is recovered uniquely from:
  (1) its opposite double-flip Boolean word, and
  (2) its original ordered (later, earlier) distinct coordinate pair.

For the FIRST OPEN WIDTH n=3 there are only three eligible coordinate
pairs (1,0), (2,0), (2,1). Thus a single target Boolean word can be
claimed by at most three actual source records, and the global original
duplicate debt is at most THREE times its distinct opposite candidates.

IMPORTANT: this bounds the REUSE LOSS but does not make any candidate
a genuine exterior hole and does not pay any other debt class.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The actual opposite double-flip word together with both original
chosen flip coordinates remembers the ENTIRE loss-collision record. -/
noncomputable def actualLossOppositePairSignature (n : ℕ)
    (a : Fin n × Fin n × (Fin n → Bool)) :
    (Fin n → Bool) × (Fin n × Fin n) :=
  (flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1,
    (a.1, a.2.1))

/-- This encoding is injective EVEN before requiring that the records
arise from genuine edges or even that their two colours be different. -/
theorem actual_loss_opposite_pair_signature_injective (n : ℕ) :
    Function.Injective (actualLossOppositePairSignature n) := by
  intro a b h
  have hword := congrArg Prod.fst h
  have hpair := congrArg Prod.snd h
  exact loss_opposite_same_coordinate_pair_injective a b
    (congrArg Prod.fst hpair) (congrArg Prod.snd hpair) hword

/-- Legal canonical earliest-prior coordinate pairs; each original
duplicate debt record has a pair j<i in this finite set. -/
def actualLossOrderedCoordinatePairs (n : ℕ) :
    Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun cd => cd.2 < cd.1)

/-- A *GLOBAL*, original-debt bound by opposite-candidate count times
the number of genuinely possible earliest-prior coordinate pairs.
No fake source tokens or credit resources appear anywhere. -/
theorem actual_loss_duplicate_debt_le_opposite_candidates_mul_ordered_pairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice ≤
      (actualLossEarliestOppositeCandidateWords C exponent choice).card *
        (actualLossOrderedCoordinatePairs n).card := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  let O := actualLossEarliestOppositeCandidateWords C exponent choice
  let P := actualLossOrderedCoordinatePairs n
  let sig : (Fin n × Fin n × (Fin n → Bool)) →
      (Fin n → Bool) × (Fin n × Fin n) :=
    actualLossOppositePairSignature n
  have hsig : Set.InjOn sig S := by
    intro a ha b hb h
    exact actual_loss_opposite_pair_signature_injective n h
  have hsub : S.image sig ⊆ O.product P := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_product.mpr
    constructor
    · change flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
        (actualEarliestLossCollisionRecords C exponent choice).image
          (fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · change (a.1, a.2.1) ∈
        (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun cd => cd.2 < cd.1)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (actual_earliest_loss_collision_record_valid
          C exponent choice a ha).2.1⟩
  calc
    translatedLossDuplicateDebt C exponent choice = S.card :=
      (actual_earliest_collision_records_card_eq_duplicate_debt
        C exponent choice).symm
    _ = (S.image sig).card := (Finset.card_image_of_injOn hsig).symm
    _ ≤ (O.product P).card := Finset.card_le_card hsub
    _ = O.card * P.card := by simp

/-- In THREE colours the only strict ordered coordinate pairs are
(1,0),(2,0),(2,1). This is an exact finite computation. -/
theorem actual_three_colour_ordered_pairs_card :
    (actualLossOrderedCoordinatePairs 3).card = 3 := by
  decide

/-- In the FIRST nontrivial open width n=3, every distinct double-
flip candidate has multiplicity at most THREE in the ORIGINAL
earliest-prior duplicate-debt ledger. In particular, the original
duplicate-debt integer cannot exceed triple the candidate count.
Eligibility of candidates as genuine holes is STILL OPEN. -/
theorem actual_three_colour_duplicate_debt_le_three_times_opposite_candidates
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3) :
    translatedLossDuplicateDebt C exponent choice ≤
      3 * (actualLossEarliestOppositeCandidateWords
        C exponent choice).card := by
  have h := actual_loss_duplicate_debt_le_opposite_candidates_mul_ordered_pairs
    C exponent choice
  rw [actual_three_colour_ordered_pairs_card] at h
  omega

#print axioms actual_loss_opposite_pair_signature_injective
#print axioms actual_loss_duplicate_debt_le_opposite_candidates_mul_ordered_pairs
#print axioms actual_three_colour_ordered_pairs_card
#print axioms actual_three_colour_duplicate_debt_le_three_times_opposite_candidates

end OrderedEdgeColoring
end JSP000404Research
