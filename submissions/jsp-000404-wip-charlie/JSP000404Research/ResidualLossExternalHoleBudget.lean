import JSP000404Research.ResidualLossTrueHoleCoverPartition
import Mathlib.Tactic

/-!
# Exact elimination of projected profile loss from the global hole budget

The six-source frontier has five non-loss obligations plus the actual
`totalDyadicProfileLoss`. Its true-hole credits are **global**, not just
within the translated-loss set.

Let U be the Boolean union of all translated-loss slices and K the global
covered set. We split *global true holes* into (U \ K) and the holes
OUTSIDE U. Combining this with the already certified three-part
profile-loss identity gives the exact iff

  otherDebt + profileLoss <= globalTrueHoles + freeSurplus
   iff
  otherDebt + coveredTranslated + duplicateDebt
              <= outsideTranslatedTrueHoles + freeSurplus.

The equivalence makes explicit which loss-associated quantities must
still be compensated. It assumes neither disjointness across slices nor
an injection into holes, and DOES NOT PROVE that either inequality holds.

One can specialize `otherDebt` to the remaining five genuine six-source
terms. `freeSurplus` must remain actual, independently unreserved credit.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Actual unoccupied Boolean words for the entire retained code. -/
noncomputable def lossLedgerGlobalTrueHoles
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)) \
    coveredCompletionWords C

/-- Global true holes not reached by ANY translated projected-loss slice. -/
noncomputable def lossLedgerOutsideTranslatedTrueHoles
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) :
    Finset (Fin n → Bool) :=
  lossLedgerGlobalTrueHoles C \
    translatedLossAllCoordinateWords C exponent choice

theorem lossLedgerGlobalTrueHoles_card_partition
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) :
    (lossLedgerGlobalTrueHoles C).card =
      (translatedLossTrueHoleWords C exponent choice).card +
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card := by
  classical
  let U := translatedLossAllCoordinateWords C exponent choice
  let K := coveredCompletionWords C
  let H := (Finset.univ : Finset (Fin n → Bool)) \ K
  have hpartition : H = (U \ K) ∪ (H \ U) := by
    ext word
    by_cases hU : word ∈ U <;> by_cases hK : word ∈ K <;>
      simp [H, hU, hK]
  have hdisjoint : Disjoint (U \ K) (H \ U) := by
    apply Finset.disjoint_left.mpr
    intro word hhit houtside
    exact (Finset.mem_sdiff.mp houtside).2
      (Finset.mem_sdiff.mp hhit).1
  change H.card = (U \ K).card + (H \ U).card
  calc
    H.card = ((U \ K) ∪ (H \ U)).card :=
      congrArg Finset.card hpartition
    _ = (U \ K).card + (H \ U).card :=
      Finset.card_union_of_disjoint hdisjoint

/-- An exact *equivalence*: after cancellation, the profile-loss
obstruction consists precisely of covered translated words and
duplicate translated words. All five other payment classes can be
collected into `otherDebt`, without presuming they are already paid. -/
theorem lossProfilePayment_iff_externalTrueHolePayment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (otherDebt freeSurplus : ℕ) :
    (otherDebt +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
      (lossLedgerGlobalTrueHoles C).card + freeSurplus) ↔
    (otherDebt +
      (translatedLossCoveredWords C exponent choice).card +
      translatedLossDuplicateDebt C exponent choice ≤
      (lossLedgerOutsideTranslatedTrueHoles
        C exponent choice).card + freeSurplus) := by
  have hprofile :=
    totalDyadicProfileLoss_eq_trueHoles_plus_covered_plus_duplicate
      C exponent hexp honeLoss choice
  have hholes :=
    lossLedgerGlobalTrueHoles_card_partition C exponent choice
  omega

#print axioms lossLedgerGlobalTrueHoles_card_partition
#print axioms lossProfilePayment_iff_externalTrueHolePayment

end OrderedEdgeColoring
end JSP000404Research
