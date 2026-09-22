
import JSP000404Research.ResidualOverlapSurplus
import Mathlib.Tactic

/-!
# Exact decomposition of projected overlap mass by residual edge

Every projected overlap word determines a unique ordered residual carrier
u<v.  Therefore the pairwise intersection sets

  Q_u inter Q_v

attached to distinct ordered residual edges are disjoint.

Conversely every word in Q_u inter Q_v for an ordered residual edge is
double-covered, because u and v are distinct and global completion
multiplicity is at most two.

Hence overlapCompletionWords is the disjoint union of the pairwise overlap
cubes over all ordered residual edges, and

  card(overlapCompletionWords)
    = sum_{u<v, residual} card(Q_u inter Q_v).

Combined with ResidualOverlapCube this turns the global overlap term into an
exact sum of powers 2^d over residual carriers.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

noncomputable def residualCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (V × V) := by
  classical
  exact ((Finset.univ : Finset V).product Finset.univ).filter
    fun p => p.1 < p.2 ∧ IsResidual C p.1 p.2

@[simp] theorem mem_residualCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (u,v) ∈ residualCarrierPairs C ↔
      u < v ∧ IsResidual C u v := by
  classical
  simp [residualCarrierPairs]

noncomputable def carrierOverlapWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (p : V × V) :
    Finset (Fin n → Bool) :=
  retainedCompletionWords C p.1 ∩
    retainedCompletionWords C p.2

@[simp] theorem mem_carrierOverlapWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (p : V × V) (word : Fin n → Bool) :
    word ∈ carrierOverlapWords C p ↔
      word ∈ retainedCompletionWords C p.1 ∧
      word ∈ retainedCompletionWords C p.2 := by
  classical
  simp [carrierOverlapWords]

/-- A word common to an ordered pair of distinct vertices is an overlap word. -/
theorem mem_overlapCompletionWords_of_common_ordered_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    word ∈ overlapCompletionWords C := by
  have huF :
      u ∈ completionFibre C word :=
    (mem_completionFibre C word u).2 huWord
  have hvF :
      v ∈ completionFibre C word :=
    (mem_completionFibre C word v).2 hvWord
  have hnontrivial :
      (completionFibre C word).Nontrivial :=
    ⟨u, huF, v, hvF, ne_of_lt huv⟩
  have hlo : 2 ≤ (completionFibre C word).card :=
    hnontrivial.two_le_card
  have hhi := completionFibre_card_le_two C word
  apply (mem_overlapCompletionWords C word).2
  omega

/-- Distinct ordered residual carriers have disjoint overlap-word sets. -/
theorem carrierOverlapWords_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    ((residualCarrierPairs C : Finset (V × V)) : Set (V × V)).PairwiseDisjoint
      (carrierOverlapWords C) := by
  classical
  intro p hp q hq hpq
  rw [Finset.disjoint_left]
  intro word hpWord hqWord
  have hpData :=
    (mem_residualCarrierPairs C p.1 p.2).1
      (by simpa using hp)
  have hqData :=
    (mem_residualCarrierPairs C q.1 q.2).1
      (by simpa using hq)
  have hpParts :=
    (mem_carrierOverlapWords C p word).1 hpWord
  have hqParts :=
    (mem_carrierOverlapWords C q word).1 hqWord
  have hoverlap :=
    mem_overlapCompletionWords_of_common_ordered_pair
      C hpData.1 hpParts.1 hpParts.2
  have huniq :=
    ordered_residual_pair_unique_of_overlapWord
      C hoverlap
      hpData.1 hqData.1
      hpParts.1 hpParts.2
      hqParts.1 hqParts.2
  apply hpq
  cases p with
  | mk pu pv =>
      cases q with
      | mk qu qv =>
          simp_all

/-- The global overlap set is exactly the disjoint union of residual-carrier
intersection cubes. -/
theorem overlapCompletionWords_eq_carrier_biUnion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    overlapCompletionWords C =
      (residualCarrierPairs C).biUnion
        (carrierOverlapWords C) := by
  classical
  apply Finset.ext
  intro word
  constructor
  · intro hoverlap
    obtain ⟨u, v, huv, hres, huWord, hvWord, _⟩ :=
      exists_ordered_residual_pair_of_overlapWord C hoverlap
    apply Finset.mem_biUnion.mpr
    refine ⟨(u,v), ?_, ?_⟩
    · exact (mem_residualCarrierPairs C u v).2
        ⟨huv, hres⟩
    · exact (mem_carrierOverlapWords C (u,v) word).2
        ⟨huWord, hvWord⟩
  · intro hword
    obtain ⟨p, hpCarrier, hpWord⟩ :=
      Finset.mem_biUnion.mp hword
    have hpData :=
      (mem_residualCarrierPairs C p.1 p.2).1
        (by simpa using hpCarrier)
    have hpParts :=
      (mem_carrierOverlapWords C p word).1 hpWord
    exact mem_overlapCompletionWords_of_common_ordered_pair
      C hpData.1 hpParts.1 hpParts.2

/-- Exact cardinal decomposition of overlap mass by ordered residual carrier. -/
theorem overlapCompletionWords_card_eq_sum_carrier_intersections
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (overlapCompletionWords C).card =
      ∑ p ∈ residualCarrierPairs C,
        (carrierOverlapWords C p).card := by
  classical
  rw [overlapCompletionWords_eq_carrier_biUnion C,
      Finset.card_biUnion
        (carrierOverlapWords_pairwiseDisjoint C)]

/-- Ordered residual carriers whose projected completion cubes actually
overlap. -/
noncomputable def overlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (V × V) := by
  classical
  exact (residualCarrierPairs C).filter fun p =>
    (carrierOverlapWords C p).Nonempty

@[simp] theorem mem_overlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (p : V × V) :
    p ∈ overlapCarrierPairs C ↔
      p ∈ residualCarrierPairs C ∧
      (carrierOverlapWords C p).Nonempty := by
  classical
  simp [overlapCarrierPairs]

theorem overlapCarrierWords_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    ((overlapCarrierPairs C : Finset (V × V)) : Set (V × V)).PairwiseDisjoint
      (carrierOverlapWords C) := by
  intro p hp q hq hpq
  have hp' :
      p ∈ residualCarrierPairs C :=
    ((mem_overlapCarrierPairs C p).1 hp).1
  have hq' :
      q ∈ residualCarrierPairs C :=
    ((mem_overlapCarrierPairs C q).1 hq).1
  exact carrierOverlapWords_pairwiseDisjoint C hp' hq' hpq

/-- Filtering away empty residual-edge intersections does not change the
global overlap union. -/
theorem overlapCompletionWords_eq_overlapCarrier_biUnion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    overlapCompletionWords C =
      (overlapCarrierPairs C).biUnion
        (carrierOverlapWords C) := by
  classical
  rw [overlapCompletionWords_eq_carrier_biUnion C]
  apply Finset.ext
  intro word
  constructor
  · intro hword
    obtain ⟨p, hp, hpWord⟩ := Finset.mem_biUnion.mp hword
    apply Finset.mem_biUnion.mpr
    refine ⟨p, ?_, hpWord⟩
    apply (mem_overlapCarrierPairs C p).2
    exact ⟨hp, ⟨word, hpWord⟩⟩
  · intro hword
    obtain ⟨p, hp, hpWord⟩ := Finset.mem_biUnion.mp hword
    apply Finset.mem_biUnion.mpr
    exact ⟨p, ((mem_overlapCarrierPairs C p).1 hp).1, hpWord⟩

/-- Exact power-of-two decomposition over the genuinely overlapping residual
carriers only. -/
theorem overlapCompletionWords_card_eq_sum_pow_commonInactive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (overlapCompletionWords C).card =
      ∑ p ∈ overlapCarrierPairs C,
        2 ^ (commonRetainedInactive C p.1 p.2).card := by
  classical
  rw [overlapCompletionWords_eq_overlapCarrier_biUnion C,
      Finset.card_biUnion
        (overlapCarrierWords_pairwiseDisjoint C)]
  apply Finset.sum_congr rfl
  intro p hp
  have hne :=
    ((mem_overlapCarrierPairs C p).1 hp).2
  obtain ⟨word, hword⟩ := hne
  have hparts :=
    (mem_carrierOverlapWords C p word).1 hword
  exact retainedCompletionWords_inter_card
    C hparts.1 hparts.2

#print axioms mem_overlapCompletionWords_of_common_ordered_pair
#print axioms carrierOverlapWords_pairwiseDisjoint
#print axioms overlapCompletionWords_eq_carrier_biUnion
#print axioms overlapCompletionWords_card_eq_sum_carrier_intersections
#print axioms overlapCompletionWords_card_eq_sum_pow_commonInactive

end OrderedEdgeColoring
end JSP000404Research
