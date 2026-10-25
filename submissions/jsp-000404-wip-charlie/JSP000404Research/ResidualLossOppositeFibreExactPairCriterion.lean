import JSP000404Research.ResidualLossCanonicalOppositeFibreBound
import Mathlib.Tactic

/-!
# Exact opposite-corner fibre: ONE determined source word per coordinate pair

Earlier work proved that each candidate q has at most one real
earliest-prior collision record for every strict ordered pair (i,j).
Here we replace the upper bound by an EXACT original-source membership
criterion. The possible original source word is not guessed: it MUST be
  flip_i (flip_j q)
because the opposite double flip is invertible.

Thus the number of collision records targeting q equals exactly the
number of original strict coordinate pairs (i,j) for which this
determined inverse word belongs to the *actual* earliest-prior
translated-loss intersection. In n=3 this is a THREE-TEST finite
source-native criterion, not a generic combinatorial upper bound.

This does not assert any candidate q is truly outside all completion
cubes, and it does not discharge the global AngleCap payment sorry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Invert the ordered genuine two-coordinate Boolean opposite map,
without a coordinate-distinctness assumption. -/
theorem opposite_doubleflip_eq_iff_original_inverse
    {n : ℕ}
    (w q : Fin n → Bool) (c d : Fin n) :
    flipBoolWordAt (flipBoolWordAt w c) d = q ↔
      w = flipBoolWordAt (flipBoolWordAt q d) c := by
  constructor
  · intro h
    have hh := congrArg
      (fun x : Fin n → Bool => flipBoolWordAt (flipBoolWordAt x d) c)
      h
    simpa only [flipBoolWordAt_involutive] using hh
  · intro h
    rw [h]
    simp only [flipBoolWordAt_involutive]

/-- Exact ORIGINAL strict earliest-prior coordinate pairs which have
a genuine duplicate-debt record targeting the concrete Boolean q.
Each pair determines its OWN inverse source word uniquely. -/
noncomputable def actualLossOppositeEligibleSourcePairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (q : Fin n → Bool) :
    Finset (Fin n × Fin n) :=
  (actualLossOrderedCoordinatePairs n).filter
    (fun cd =>
      flipBoolWordAt (flipBoolWordAt q cd.2) cd.1 ∈
        lossEarliestPairWords
          (lossSliceAtNat C exponent choice) cd.1.val cd.2.val)

/-- Every actual record with opposite q passes the exact original
earliest-prior source predicate at its ordered pair. -/
theorem actual_loss_opposite_fibre_pair_in_exact_source_pairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (q : Fin n → Bool)
    (a : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualLossOppositeCandidateFibre C exponent choice q) :
    (a.1, a.2.1) ∈
      actualLossOppositeEligibleSourcePairs C exponent choice q := by
  classical
  obtain ⟨hrecord, hopposite⟩ := Finset.mem_filter.mp ha
  obtain ⟨horder, hsrc⟩ := (Finset.mem_filter.mp hrecord).2
  change (a.1, a.2.1) ∈
    (actualLossOrderedCoordinatePairs n).filter
      (fun cd =>
        flipBoolWordAt (flipBoolWordAt q cd.2) cd.1 ∈
          lossEarliestPairWords
            (lossSliceAtNat C exponent choice) cd.1.val cd.2.val)
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, horder⟩
  · have hinverse :=
      (opposite_doubleflip_eq_iff_original_inverse
        a.2.2 q a.1 a.2.1).mp hopposite
    simpa only [← hinverse] using hsrc

/-- Conversely, an original ordered pair satisfying the exact source
criterion yields a real unique earliest-prior debt record with that
opposite candidate, not a fabricated possible square. -/
theorem actual_loss_opposite_exact_source_pair_has_record
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (q : Fin n → Bool)
    (cd : Fin n × Fin n)
    (hcd : cd ∈ actualLossOppositeEligibleSourcePairs C exponent choice q) :
    ∃ a ∈ actualLossOppositeCandidateFibre C exponent choice q,
      (a.1, a.2.1) = cd := by
  classical
  obtain ⟨hpair, hsrc⟩ := Finset.mem_filter.mp hcd
  have horder := (Finset.mem_filter.mp hpair).2
  let w : Fin n → Bool := flipBoolWordAt (flipBoolWordAt q cd.2) cd.1
  let a : Fin n × Fin n × (Fin n → Bool) := (cd.1, cd.2, w)
  have hrecord : a ∈ actualEarliestLossCollisionRecords C exponent choice := by
    change a ∈ (Finset.univ : Finset (Fin n × Fin n × (Fin n → Bool))).filter
      (fun a => a.2.1 < a.1 ∧
        a.2.2 ∈ lossEarliestPairWords
          (lossSliceAtNat C exponent choice) a.1.val a.2.1.val)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, horder, hsrc⟩
  refine ⟨a, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨hrecord, ?_⟩
  exact (opposite_doubleflip_eq_iff_original_inverse w q cd.1 cd.2).mpr rfl

/-- EXACT finite fibre cardinality, not merely a 3x upper bound:
count strict original coordinate pairs for which the inverse word
really belongs to the earlier first-appearance loss intersection. -/
theorem actual_loss_opposite_candidate_fibre_card_eq_exact_source_pairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (q : Fin n → Bool) :
    (actualLossOppositeCandidateFibre C exponent choice q).card =
      (actualLossOppositeEligibleSourcePairs C exponent choice q).card := by
  classical
  let F := actualLossOppositeCandidateFibre C exponent choice q
  let P := actualLossOppositeEligibleSourcePairs C exponent choice q
  let pair : Fin n × Fin n × (Fin n → Bool) → Fin n × Fin n :=
    fun a => (a.1, a.2.1)
  have hinj : Set.InjOn pair F :=
    actual_loss_opposite_fibre_coordinate_pair_injOn C exponent choice q
  have hEq : F.image pair = P := by
    ext cd
    constructor
    · intro hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact actual_loss_opposite_fibre_pair_in_exact_source_pairs
        C exponent choice q a ha
    · intro hz
      obtain ⟨a, ha, hpair⟩ :=
        actual_loss_opposite_exact_source_pair_has_record
          C exponent choice q cd hz
      exact Finset.mem_image.mpr ⟨a, ha, hpair⟩
  calc
    F.card = (F.image pair).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = P.card := congrArg Finset.card hEq

#print axioms opposite_doubleflip_eq_iff_original_inverse
#print axioms actual_loss_opposite_fibre_pair_in_exact_source_pairs
#print axioms actual_loss_opposite_exact_source_pair_has_record
#print axioms actual_loss_opposite_candidate_fibre_card_eq_exact_source_pairs

end OrderedEdgeColoring
end JSP000404Research
