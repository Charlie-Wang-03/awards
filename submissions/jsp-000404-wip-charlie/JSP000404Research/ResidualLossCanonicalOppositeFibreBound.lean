import JSP000404Research.ResidualLossCanonicalOppositeSignatureBound
import Mathlib.Tactic

/-!
# Fibrewise original-source multiplicity of canonical loss-collision opposite corners

The global signature injection proves Ddup <= |O| * choose(n,2).
Here the bound is resolved SOURCE-BY-SOURCE for each one ACTUAL opposite
Boolean word q: a collision fibre is injected into the STRICT
earliest-prior coordinate pairs j<i, and so a single candidate can
represent at most three genuine debt records when n=3.

Crucially, the fibre definition uses original real collision records,
not arbitrary ordered pairs or dummy sources. No opposite candidate is
assumed to be a true exterior hole, and this does not solve AngleCap.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Every ACTUAL earliest-prior translated-loss collision debt record
which asks for the same concrete opposite double-flip Boolean word q. -/
noncomputable def actualLossOppositeCandidateFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (q : Fin n → Bool) :
    Finset (Fin n × Fin n × (Fin n → Bool)) :=
  (actualEarliestLossCollisionRecords C exponent choice).filter
    (fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 = q)

/-- One opposite corner cannot be demanded twice by different
original words from the SAME exact earliest-prior coordinate pair.
This is a fibre-level true injection, not a counting approximation. -/
theorem actual_loss_opposite_fibre_coordinate_pair_injOn
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (q : Fin n → Bool) :
    Set.InjOn
      (fun a : Fin n × Fin n × (Fin n → Bool) => (a.1, a.2.1))
      (actualLossOppositeCandidateFibre C exponent choice q) := by
  intro a ha b hb hp
  have ha' : flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 = q :=
    (Finset.mem_filter.mp ha).2
  have hb' : flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1 = q :=
    (Finset.mem_filter.mp hb).2
  have hc : a.1 = b.1 :=
    congrArg (fun pair : Fin n × Fin n => pair.1) hp
  have hd : a.2.1 = b.2.1 :=
    congrArg (fun pair : Fin n × Fin n => pair.2) hp
  exact loss_opposite_same_coordinate_pair_injective a b hc hd
    (ha'.trans hb'.symm)

/-- For every n and EVERY candidate q, source-native multiplicity
is bounded by the number of strictly ordered earliest-prior pairs.
In particular this excludes repeated genuine claims inside a pair. -/
theorem actual_loss_opposite_fibre_card_le_ordered_pairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (q : Fin n → Bool) :
    (actualLossOppositeCandidateFibre C exponent choice q).card ≤
      (actualLossOrderedCoordinatePairs n).card := by
  classical
  let F := actualLossOppositeCandidateFibre C exponent choice q
  let P := actualLossOrderedCoordinatePairs n
  let pair : Fin n × Fin n × (Fin n → Bool) → Fin n × Fin n :=
    fun a => (a.1, a.2.1)
  have hinj : Set.InjOn pair F :=
    actual_loss_opposite_fibre_coordinate_pair_injOn C exponent choice q
  have hsub : F.image pair ⊆ P := by
    intro cd hcd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hcd
    have hsource :
        a ∈ actualEarliestLossCollisionRecords C exponent choice :=
      (Finset.mem_filter.mp ha).1
    change (a.1, a.2.1) ∈
      (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun cd => cd.2 < cd.1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (actual_earliest_loss_collision_record_valid
        C exponent choice a hsource).2.1⟩
  calc
    F.card = (F.image pair).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ P.card := Finset.card_le_card hsub

/-- The first unresolved colour width is n=3. For EACH genuine
candidate q individually, the maximum multiplicity of ACTUAL original
earliest-prior duplicate-debt source records is THREE, no matter how
many original planar centres there are. This does NOT count usable
outside-translated true holes. -/
theorem actual_three_colour_opposite_candidate_fibre_card_le_three
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (q : Fin 3 → Bool) :
    (actualLossOppositeCandidateFibre C exponent choice q).card ≤ 3 := by
  have h := actual_loss_opposite_fibre_card_le_ordered_pairs
    C exponent choice q
  simpa only [actual_three_colour_ordered_pairs_card] using h

#print axioms actual_loss_opposite_fibre_coordinate_pair_injOn
#print axioms actual_loss_opposite_fibre_card_le_ordered_pairs
#print axioms actual_three_colour_opposite_candidate_fibre_card_le_three

end OrderedEdgeColoring
end JSP000404Research
